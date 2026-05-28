"""
Lean 4 REPL subprocess wrapper.

Manages a long-running `lake exe repl` process, communicating via JSON
over stdin/stdout. Implements the LeanExecutor protocol.

Protocol (discovered via testing):
    - Launch:  lake exe repl from lean_project directory
    - Send:    json.dumps(payload) + "\\n\\n"  (blank line terminator)
    - Read:    lines until blank line, join, parse as JSON

    Initialize proof:
        send: {"cmd": "theorem ... := by\\n  sorry"}
        recv: {"sorries": [{"proofState": 0, "goal": "⊢ ..."}], "env": 0}

    Apply tactic:
        send: {"tactic": "simp", "proofState": 0}
        recv: {"proofState": 1, "goals": ["n : Nat\\n⊢ n + 0 = n"]}  # incomplete
        recv: {"proofState": 2, "goals": [], "proofStatus": "Completed"}  # done
        recv: {"message": "Lean error:\\n..."}  # failed

    Branching:
        Send two different tactics with the same proofState N.
        Each gets an independent new proofState number.
        This is how we explore multiple branches without restarting Lean.

Here is the full compute hierarchy:

SubprocessExecutor (SubprocessExecutor and all its LeanWorker management runs in one Python process. The SubprocessExecutor is
a lightweight Python coordinator for our LeanWorkers. Each LeanWorker spawns a "lake exe repl" OS subprocess with separate PID, separate memory), but the Python side is single-process event loop.
│
│  owns:
│  ├── _capacity (int)
│  ├── _workers: list[LeanWorker]       # flat list, for shutdown
│  └── _pool: asyncio.Queue[LeanWorker] # the queue workers are borrowed from
│
└── LeanWorker  (one per capacity slot, actual OS process, meaning we have a unique PID and memory for each LeanWorker)
    │
    │  owns:
    │  ├── _proc: asyncio.subprocess.Process   ← one lake exe repl OS process
    │  └── _proof_state_cache: dict[str, int]  ← hash → REPL integer ID
    │
    └── lake exe repl  (one OS process per worker)
        │
        │  owns (internal to Lean, not visible to Python):
        │  ├── loaded Mathlib environment
        │  └── proof state table: { 0: <state>, 1: <state>, 2: <state>, ... }

A single SubprocessExecutor with multiple workers is sufficient.
Each worker maintains its own REPL process and proof state cache, but they all share the same underlying Lean environment on disk (the lean_project directory).
This allows us to explore multiple branches of the proof tree in parallel without needing to restart the REPL for each branch. 
Each worker can be working on the same theorem, or different theorems, and they are working all in parallel.

"""

from __future__ import annotations

import asyncio
import dataclasses
import json
import logging
import os
import time
import uuid
from pathlib import Path
from typing import Optional

from core.executor import LeanExecutor, StepResult
from core.proof_state import Goal, Hypothesis, ProofState

logger = logging.getLogger(__name__)

# Path to the lean_project directory — where lake exe repl is run from
# Think of a lean project as something that is similar to a python virtual environment - 
# it contains the Lean files, dependencies, and compiled artifacts needed to run the REPL.
LEAN_PROJECT_DIR = Path(__file__).parent.parent / "lean_project"


class LeanREPLError(Exception):
    """Raised when the REPL process dies or returns unexpected output."""
    pass


class LeanWorker:
    """
    A single Lean REPL worker process.

    Wraps one `lake exe repl` subprocess. Manages the proof state cache
    that maps ProofState hashes to REPL proofState numbers.

    Not thread-safe — use one worker per asyncio task, or protect with
    a semaphore (which SubprocessExecutor does via its worker pool).

    Each LeanWorker is a completely separate "lake exe repl" OS subprocess, and
    there is no shared memory between lean workers.
    """

    def __init__(self, lean_project_dir: Path):
        self._dir = lean_project_dir
        self._proc: Optional[asyncio.subprocess.Process] = None
        # Maps stable_hash -> proofState number in the REPL
        self._proof_state_cache: dict[str, int] = {}

    async def start(self) -> None:
        """Launch the lake exe repl subprocess.
        
        worker.start(): launches the Lean subprocess using asyncio.create_subprocess_exec() and sets up the REPL.
        In the mock, we just need it to be an async function that does nothing, since we won't actually start a real REPL. asyncio.create_subprocess_exec()
        itself is an async operation - it asks the OS to spawn a new process, which takes a small amount of time. While the OS is doing that, other coroutines can run.
        So start() must be async because it "awaits" the subprocess creation.

        "lake exe repl" acts exactly like typing "python" in a terminal, and acts as an interactive REPL. All inputs must be in JSON format separated by a blank line. For ex.,

        $ lake exe repl
        {"cmd": "#check Nat.add_zero"}

        {"messages": [...], "env": 0}

        {"tactic": "intro n", "proofState": 0}

        {"proofState": 1, "goals": [...]}

        Also, a process is a running instance of a program. When the process is launched, it has its own memory space, file handles, and system resources.
        In our case, each LeanWorker launches its own "lake exe repl" process, which means each worker has its own separate instance of the Lean REPL running 
        in parallel. This allows us to explore multiple branches of the proof tree simultaneously without interference,
        since each REPL process maintains its own proof state table and environment.
        
        """
        self._proc = await asyncio.create_subprocess_exec(
            "lake", "exe", "repl",
            stdin=asyncio.subprocess.PIPE,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.DEVNULL,
            cwd=str(self._dir),
        )
        logger.debug(f"Started Lean worker pid={self._proc.pid}")

    async def stop(self) -> None:
        """Terminate the subprocess cleanly.
        
        worker.stop(): stop() waits for the subprocess to terminate cleanly. self._proc.wait() blocks until the Lean process actually exits.
    That could take a moment - Lean needs to flush its output and shut down. Rather than freezing python while waiting, "await" lets other things run in the meantime.
        
        """
        if self._proc and self._proc.returncode is None:
            try:
                self._proc.stdin.close()
                await asyncio.wait_for(self._proc.wait(), timeout=5.0)
            except asyncio.TimeoutError:
                self._proc.kill()
                await self._proc.wait()
        logger.debug("Lean worker stopped")

    async def _send(self, payload: dict) -> dict:
        """
        Send a JSON payload to the REPL and read the response.
        Every command is terminated with \\n\\n (blank line).
        Every response is terminated with a blank line.
        """
        if not self._proc or self._proc.returncode is not None:
            raise LeanREPLError("Lean worker process is not running")

        msg = (json.dumps(payload) + "\n\n").encode()
        self._proc.stdin.write(msg)
        await self._proc.stdin.drain()

        # Read lines until we hit a blank line
        lines = []
        while True:
            try:
                line = await asyncio.wait_for(
                    self._proc.stdout.readline(),
                    timeout=30.0,
                )
            except asyncio.TimeoutError:
                raise LeanREPLError(
                    f"Lean REPL timed out waiting for response to: {payload}"
                )
            decoded = line.decode()
            if decoded.strip() == "":
                break
            lines.append(decoded)

        if not lines:
            raise LeanREPLError("Lean REPL returned empty response")

        return json.loads("".join(lines))

    async def reset(self, theorem: str) -> tuple[ProofState, int]:
        """
        Initialize a new proof attempt.

        Sends the theorem with a sorry placeholder to get the initial
        proof state. Returns (ProofState, repl_proof_state_id).
        Note that "sorry" is a special Lean placeholder that creates an open goal,
        allowing us to extract the initial proof state without needing a complete proof. 
        It allows us to get the initial goal state without proving the theorem, which is perfect for our search loop.
        We will replace "sorry" with actual tactics as we explore the proof tree.
        The REPL returns this initial state along with a unique proofState id that we cache
        for future tactic applications. Think of "sorry" as a "TODO" in Lean.

        worker.reset(): In general reset() sends the theorem statement to the REPL and waits for the initial proof state. This involves multiple async steps:
        1. Send the theorem statement to the REPL (async because it writes to the subprocess stdin).
        2. Wait for the REPL to respond with the initial proof state (async because it reads from the subprocess stdout).

        Args:
            theorem: A complete Lean 4 theorem statement ending with := by

        Returns:
            (initial_proof_state, repl_proof_state_id)
        """
        # Format: "theorem foo : <stmt> := by\n  sorry"
        if ":= by" not in theorem:
            theorem = theorem.rstrip() + " := by"
        cmd = theorem + "\n  sorry"

        response = await self._send({"cmd": cmd})

        # Check for parse errors
        if "message" in response and "sorries" not in response:
            error_msg = response.get("message", "Unknown error")
            error_state = ProofState(goals=(), error=error_msg)
            return error_state, -1

        # Check for Lean errors in messages
        messages = response.get("messages", [])
        errors = [m for m in messages if m.get("severity") == "error"]
        if errors:
            error_msg = errors[0].get("data", "Lean error")
            error_state = ProofState(goals=(), error=error_msg)
            return error_state, -1

        # Extract proof state from sorries
        sorries = response.get("sorries", [])
        if not sorries:
            # No sorries means theorem was proved trivially
            closed_state = ProofState(goals=())
            return closed_state, -1

        sorry = sorries[0]
        repl_ps_id = sorry["proofState"]
        goal_str = sorry.get("goal", "")

        # Parse the goal string into our ProofState structure
        initial_state = _parse_goal_string(goal_str)

        # Cache this proof state
        self._proof_state_cache[initial_state.stable_hash()] = repl_ps_id

        return initial_state, repl_ps_id

    async def step(
        self,
        state: ProofState,
        tactic: str,
    ) -> StepResult:
        """
        Apply a tactic to a proof state.

        Looks up the REPL proofState id for the given state, sends the
        tactic, and parses the response into a StepResult.

        worker.step(): step() sends a tactic to the REPL and waits for the result. This also involves multiple async steps:
        1. Send the tactic to the REPL (async because it writes to the subprocess stdin).
        2. Wait for the REPL to respond with the new proof state and success/failure info (async because it reads from the subprocess stdout).
        """
        start = time.perf_counter()

        # Look up the REPL proof state id for this state
        repl_ps_id = self._proof_state_cache.get(state.stable_hash())
        if repl_ps_id is None:
            # State not in cache — return error
            error_state = ProofState(
                goals=state.goals,
                error=f"proof state not found in REPL cache",
                depth=state.depth,
                tactic_trace=state.tactic_trace,
            )
            return StepResult(
                next_state=error_state,
                tactic=tactic,
                elapsed_ms=(time.perf_counter() - start) * 1000,
            )

        # Send tactic to REPL
        try:
            response = await self._send({
                "tactic": tactic,
                "proofState": repl_ps_id,
            })
        except LeanREPLError as e:
            error_state = ProofState(
                goals=state.goals,
                error=str(e),
                depth=state.depth,
                tactic_trace=state.tactic_trace,
            )
            return StepResult(
                next_state=error_state,
                tactic=tactic,
                elapsed_ms=(time.perf_counter() - start) * 1000,
            )

        elapsed = (time.perf_counter() - start) * 1000

        # Parse response
        if "message" in response:
            # Tactic failed
            error_state = ProofState(
                goals=state.goals,
                error=response["message"],
                depth=state.depth,
                tactic_trace=state.tactic_trace,
            )
            return StepResult(
                next_state=error_state,
                tactic=tactic,
                elapsed_ms=elapsed,
            )

        # Tactic succeeded
        new_repl_ps_id = response["proofState"]
        goals_raw = response.get("goals", [])
        proof_status = response.get("proofStatus", "")

        if not goals_raw or proof_status == "Completed":
            # Proof closed
            closed_state = ProofState(
                goals=(),
                depth=state.depth + 1,
                tactic_trace=state.tactic_trace + (tactic,),
            )
            return StepResult(
                next_state=closed_state,
                tactic=tactic,
                elapsed_ms=elapsed,
            )

        # Parse new goals
        new_goals = tuple(
            _parse_goal_string(g) .goals[0]
            for g in goals_raw
            if _parse_goal_string(g).goals
        )

        next_state = ProofState(
            goals=new_goals,
            depth=state.depth + 1,
            tactic_trace=state.tactic_trace + (tactic,),
        )

        # Cache the new proof state
        self._proof_state_cache[next_state.stable_hash()] = new_repl_ps_id

        return StepResult(
            next_state=next_state,
            tactic=tactic,
            elapsed_ms=elapsed,
        )


class SubprocessExecutor:
    """
    Pool of LeanWorker processes implementing the LeanExecutor protocol.

    Each worker owns a separate `lake exe repl` subprocess with its own
    proof state table. REPL proof-state IDs are process-local integers,
    so a state created by worker A cannot be used by worker B.

    To handle this, SubprocessExecutor maintains a _router that maps
    each ProofState's stable_hash to the worker index that owns it.
    reset() assigns a worker via round-robin; step() always routes to
    the worker that owns the given state.

    Parallelism: concurrent step() calls on states owned by different
    workers run simultaneously. Calls on the same state are serialized
    through its worker's lock (correct, since the REPL is single-threaded).

    On MacBook Air (8GB): capacity=2
    On a larger machine like DGX Spark (128GB): capacity=10
    """

    def __init__(
        self,
        lean_project_dir: Path = LEAN_PROJECT_DIR,
        capacity: int = 2,
    ):
        self._dir = lean_project_dir
        self._capacity = capacity
        self._workers: list[LeanWorker] = []
        self._locks: list[asyncio.Lock] = []
        # Maps (session_id, stable_hash) -> index into self._workers.
        # Using session_id as part of the key lets multiple independent
        # proof attempts on the same theorem coexist without collision.
        self._router: dict[tuple[str, str], int] = {}
        self._rr_counter = 0
        self._started = False

    @property
    def capacity(self) -> int:
        return self._capacity

    async def start(self) -> None:
        """Start all worker processes. Must be called before use."""
        for _ in range(self._capacity):
            worker = LeanWorker(self._dir)
            await worker.start()
            self._workers.append(worker)
            self._locks.append(asyncio.Lock())
        self._started = True
        logger.info(f"Started {self._capacity} Lean workers")

    async def reset(self, theorem: str) -> ProofState:
        """Initialize a proof attempt, assigning a worker via round-robin.

        Generates a unique session_id and stamps it on the returned state.
        All subsequent step() calls must use states carrying this session_id
        so the router can distinguish parallel attempts on the same theorem.
        """
        idx = self._rr_counter % self._capacity
        self._rr_counter += 1
        async with self._locks[idx]:
            state, _ = await self._workers[idx].reset(theorem)
        if not state.is_error:
            session_id = str(uuid.uuid4())
            state = dataclasses.replace(state, session_id=session_id)
            self._router[(session_id, state.stable_hash())] = idx
        return state

    async def step(self, state: ProofState, tactic: str) -> StepResult:
        """Apply a tactic, routing to the worker that owns this state.

        Uses (session_id, stable_hash) to look up the owning worker, so
        two sessions on the same theorem never interfere with each other.
        Stamps session_id onto the resulting state so it continues to route
        correctly for all subsequent steps.
        """
        key = (state.session_id, state.stable_hash())
        idx = self._router.get(key)
        if idx is None:
            error_state = dataclasses.replace(
                state,
                error="proof state not routable: no worker owns this state",
            )
            return StepResult(next_state=error_state, tactic=tactic)
        async with self._locks[idx]:
            result = await self._workers[idx].step(state, tactic)
        if result.success:
            next_state = dataclasses.replace(result.next_state, session_id=state.session_id)
            self._router[(state.session_id, next_state.stable_hash())] = idx
            result = dataclasses.replace(result, next_state=next_state)
        return result

    async def close(self) -> None:
        """Shut down all worker processes."""
        for worker in self._workers:
            await worker.stop()
        self._workers.clear()
        self._locks.clear()
        self._router.clear()
        logger.info("All Lean workers stopped")


# ---------------------------------------------------------------------------
# Parsing helpers
# ---------------------------------------------------------------------------

def _parse_goal_string(goal_str: str) -> ProofState:
    """
    Parse a Lean goal string into a ProofState.

    Input format (from REPL):
        "n : Nat\\nh : n > 0\\n⊢ n + 0 = n"

    Output:
        Usually a goal looks like:

        n : Nat
        h : n > 0
        ⊢ n + 0 = n

        targets start with symbol turnstile "⊢",
        and hypotheses must contain ":"

        Returns a ProofState with one Goal containing the hypotheses(tuple of Hypothesis) and target(str).
    """
    if not goal_str.strip():
        return ProofState(goals=())

    lines = goal_str.strip().split("\n")

    hypotheses = []
    target = None

    for line in lines:
        line = line.strip()
        if line.startswith("⊢"):
            target = line[1:].strip()
        elif " : " in line and not line.startswith("⊢"):
            # only split at the first occurence, hence 1 as second argument
            parts = line.split(" : ", 1)
            if len(parts) == 2:
                hypotheses.append(Hypothesis(
                    name=parts[0].strip(), #for ex., name=
                    type_=parts[1].strip(),
                ))

    if target is None:
        # No turnstile found — treat whole string as target
        target = goal_str.strip()

    goal = Goal(
        hypotheses=tuple(hypotheses),
        target=target,
    )
    return ProofState(goals=(goal,))
