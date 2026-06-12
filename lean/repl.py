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

Compute hierarchy (one SubprocessExecutor = one search worker):

SubprocessExecutor  (thin Python coordinator, one per BestFirstSearch instance)
│
└── LeanWorker  (one lake exe repl OS subprocess, unique PID and memory)
    │
    │  owns:
    │  ├── _proc: asyncio.subprocess.Process   ← one lake exe repl OS process
    │  └── _proof_state_cache: dict[str, int]  ← stable_hash → REPL integer ID
    │
    └── lake exe repl  (one OS process)
        │
        │  owns (internal to Lean, not visible to Python):
        │  ├── loaded Mathlib environment
        │  └── proof state table: { 0: <state>, 1: <state>, 2: <state>, ... }

For k parallel proof searches, create k SubprocessExecutor instances and run
k BestFirstSearch.prove() coroutines concurrently with asyncio.gather().
Each executor owns exactly one worker process, so there is no cross-worker
routing or session tracking needed.
"""

from __future__ import annotations

import asyncio
import json
import logging
import os
import time
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

    Because LeanWorker methods are async, we see that SubprocessExecutor methods are also async.
    Recall that async functions are functions that can be paused and resumed, allowing other code to run while waiting for long-running operations.
    In our case, the long-running operations are the interactions with the REPL subprocess, which involve I/O and can take some time to complete.
    By making these methods async, we can ensure that our Python event loop remains responsive and can handle multiple proof attempts in parallel
    without blocking on any single REPL interaction.
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
        # start the lean REPL subprocess.
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

    async def _send(self, payload: dict, timeout: float = 30.0) -> dict:
        """
        Send a JSON payload to the REPL and read the response. Every command is terminated with \\n\\n (blank line).
        Every response is terminated with a blank line. _send() in LeanWorker.step(), where we send a tactic(part of the payload)
        to the REPL on the worker and wait for the response. 

        As an example of how async and await works, when Python gets to "await self._proc.stdin.drain()", it sends the command to the REPL
        and then pauses the current coroutine, allowing other coroutines to run while waiting for the REPL to respond. Once the REPL responds
        and the command is fully sent, the coroutine resumes and continues to read the response from the REPL.
        This allows us to handle multiple proof attempts in parallel without blocking on any single REPL interaction.

        The await points are exactly where Python steps aside and lets the OS and the Lean process do their work. Lean can take hundreds of milliseconds
        to verify a tactic, and during that time, other workers can continue to run and interact with their
        own REPL proceses.
        """
        # sanity check. We should have used LeanWorker.start() to launch the REPL before calling _send()
        if not self._proc or self._proc.returncode is not None:
            raise LeanREPLError("Lean worker process is not running")

        # .encode() converts the string to bytes, which is what the subprocess stdin expects. json.dumps() converts the payload dictionary
        # to a JSON-formatted string. We add the blank line terminator "\n\n" as required by the REPL protocol. 
        msg = (json.dumps(payload) + "\n\n").encode()
        # note that we do not need to use any lean specific python libraries to interact with the REPL.
        # Think of "lake exe repl" as a compiled Lean binary that runs as an interactive process.
        # It: 1) starts up, loads Mathlib into memory, 2)and then sits there waiting for JSON commands on stdin,
        #.    3) responds with JSON on stdout. We can interact with it using standard python subprocess communication patterns
        self._proc.stdin.write(msg)
        # drain() waits until the write buffer is flushed, meaning that the message has actually been sent to the REPL process.
        # This is important because we ensure that the command is fully sent before we start waiting for the response.
        await self._proc.stdin.drain()

        # Read lines until we hit a blank line
        lines = []
        while True:
            try:
                line = await asyncio.wait_for(
                    self._proc.stdout.readline(),
                    timeout=timeout,
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
        Apply a tactic to a proof state. Used in SubprocessExecutor.step().

        Looks up the REPL proofState id for the given state, sends the
        tactic, and parses the response into a StepResult.

        worker.step(): step() sends a tactic to the REPL and waits for the result. This also involves multiple async steps:
        1. Send the tactic to the REPL (async because it writes to the subprocess stdin).
        2. Wait for the REPL to respond with the new proof state and success/failure info (async because it reads from the subprocess stdout).
        """
        start = time.perf_counter()

        # Look up the REPL proof state id for this state, stable_hash identifies which branch of the proof tree we are on within the workers' REPL process.
        repl_ps_id = self._proof_state_cache.get(state.stable_hash())
        # error out if we dont have this state in our cache. This should not happen if our caching and routing logic is correct, 
        # but we check just in case.
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

        # Send tactic to REPL, send tactic (a string) to the given proofState id.
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

        # Parse response. Note that response is a JSON object which contains keys like proofState, goals, proofStatus, etc...
        if "message" in response:
            # Tactic failed (REPL top-level error string)
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

        # The REPL can also report errors via a "messages" list even when it
        # returns goals:[] — e.g. `exact bad_term` closes the goal syntactically
        # but reports "Unknown identifier" in messages. Treat those as failures.
        msg_errors = [
            m for m in response.get("messages", [])
            if m.get("severity") == "error"
        ]
        if msg_errors:
            error_msg = "Lean error:\n" + msg_errors[0].get("data", "unknown error")
            error_state = ProofState(
                goals=state.goals,
                error=error_msg,
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
    Wraps a single LeanWorker, implementing the LeanExecutor protocol.

    One SubprocessExecutor = one `lake exe repl` subprocess = one proof search.
    For k parallel searches, create k SubprocessExecutor instances and run
    them concurrently with asyncio.gather().

    The lock serializes reset() and step() so the REPL's stdin/stdout
    is never written to concurrently within the same Python process.
    """

    def __init__(
        self,
        lean_project_dir: Path = LEAN_PROJECT_DIR,
    ):
        self._dir = lean_project_dir
        self._worker: Optional[LeanWorker] = None
        self._lock = asyncio.Lock()
        self._started = False

    async def start(self) -> None:
        """Start the Lean worker process. Must be called before use."""
        self._worker = LeanWorker(self._dir)
        await self._worker.start()
        self._started = True
        logger.info("Started Lean worker")

    async def reset(self, theorem: str) -> ProofState:
        """Initialize a new proof attempt and return the initial ProofState."""
        async with self._lock:
            state, _ = await self._worker.reset(theorem)
        return state

    async def step(self, state: ProofState, tactic: str) -> StepResult:
        """Apply a tactic to the given proof state and return the result.

        The REPL is single-threaded, so the lock ensures that concurrent
        Python callers do not interleave their writes to stdin/stdout.

        The REPL supports branching: sending two different tactics with the
        same proofState ID produces two independent new proof states.

            send: {"tactic": "intro n", "proofState": 0}
            recv: {"proofState": 1, "goals": [...]}

            send: {"tactic": "simp", "proofState": 0}   ← same ID
            recv: {"proofState": 2, "goals": [...]}       ← independent new ID

        This lets the search explore multiple branches from one state without
        restarting the REPL, since each branch gets its own ID in the REPL's
        internal proof state table.
        """
        async with self._lock:
            return await self._worker.step(state, tactic)

    async def close(self) -> None:
        """Shut down the worker process."""
        if self._worker:
            await self._worker.stop()
            self._worker = None
        logger.info("Lean worker stopped")


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
