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
    """

    def __init__(self, lean_project_dir: Path):
        self._dir = lean_project_dir
        self._proc: Optional[asyncio.subprocess.Process] = None
        # Maps stable_hash -> proofState number in the REPL
        self._proof_state_cache: dict[str, int] = {}

    async def start(self) -> None:
        """Launch the lake exe repl subprocess."""
        self._proc = await asyncio.create_subprocess_exec(
            "lake", "exe", "repl",
            stdin=asyncio.subprocess.PIPE,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.DEVNULL,
            cwd=str(self._dir),
        )
        logger.debug(f"Started Lean worker pid={self._proc.pid}")

    async def stop(self) -> None:
        """Terminate the subprocess cleanly."""
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

    Maintains a pool of `capacity` workers. Each step() call acquires
    a worker from the pool, uses it, and returns it. This allows
    concurrent tactic verification up to the pool size.

    On MacBook Air (8GB): capacity=2
    On DGX Spark (128GB): capacity=10
    """

    def __init__(
        self,
        lean_project_dir: Path = LEAN_PROJECT_DIR,
        capacity: int = 2,
    ):
        self._dir = lean_project_dir
        self._capacity = capacity
        self._workers: list[LeanWorker] = []
        self._pool: asyncio.Queue[LeanWorker] = asyncio.Queue()
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
            await self._pool.put(worker)
        self._started = True
        logger.info(f"Started {self._capacity} Lean workers")

    async def reset(self, theorem: str) -> ProofState:
        """Initialize a proof attempt on any available worker."""
        worker = await self._pool.get()
        try:
            state, _ = await worker.reset(theorem)
            return state
        finally:
            await self._pool.put(worker)

    async def step(self, state: ProofState, tactic: str) -> StepResult:
        """Apply a tactic using any available worker."""
        worker = await self._pool.get()
        try:
            return await worker.step(state, tactic)
        finally:
            await self._pool.put(worker)

    async def close(self) -> None:
        """Shut down all worker processes."""
        for worker in self._workers:
            await worker.stop()
        self._workers.clear()
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
        ProofState with one Goal containing the hypotheses and target.
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
            parts = line.split(" : ", 1)
            if len(parts) == 2:
                hypotheses.append(Hypothesis(
                    name=parts[0].strip(),
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
