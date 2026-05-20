"""
Abstract interface for the Lean executor (tactic verifier).

The LeanExecutor protocol defines the contract for sending tactics to Lean
and getting back new proof states. The search algorithm talks exclusively
to this interface — it never imports from lean/ directly.

Implementations:
    lean/executor.py  -> SubprocessExecutor  (real Lean REPL, Phase 1+)
    lean/mock.py      -> MockExecutor        (testing, no Lean required)
"""

from __future__ import annotations
from dataclasses import dataclass
from typing import Protocol, runtime_checkable

from core.proof_state import ProofState


@dataclass(frozen=True)
class StepResult:
    """
    The result of applying a single tactic to a proof state.

    Exactly one of (next_state,) will be set depending on outcome:
        - Tactic succeeded: next_state is the new ProofState (may be closed)
        - Tactic failed:    next_state has error set, goals unchanged

    Attributes:
        next_state:   The proof state after applying the tactic.
        tactic:       The tactic that was applied. Stored for logging.
        elapsed_ms:   How long Lean took to verify this tactic. Used to
                      track REPL latency and detect hangs.
    """
    next_state: ProofState
    tactic: str
    elapsed_ms: float = 0.0

    @property
    def success(self) -> bool:
        """True if the tactic was accepted by Lean without error."""
        return not self.next_state.is_error

    @property
    def proof_closed(self) -> bool:
        """True if this tactic closed all remaining goals."""
        return self.next_state.is_closed


@runtime_checkable
class LeanExecutor(Protocol):
    """
    Protocol for sending tactics to Lean and receiving proof states.

    The search loop uses this to:
        1. Initialize a proof attempt:   reset(theorem) -> ProofState
        2. Apply a tactic:               step(state, tactic) -> StepResult
        3. Query parallelism capacity:   capacity -> int

    The capacity property is critical for hardware scaling. On a MacBook
    Air with 8GB RAM, capacity=2. On a DGX Spark with 128GB, capacity=10.
    The search loop uses this to automatically bound its parallelism —
    no hardcoded constants anywhere in the search code.
    """

    @property
    def capacity(self) -> int:
        """
        How many concurrent step() calls this executor can handle.
        The search loop uses asyncio.Semaphore(executor.capacity) to
        bound parallelism automatically.
        """
        ...

    async def reset(self, theorem: str) -> ProofState:
        """
        Start a new proof attempt for the given theorem statement.

        Args:
            theorem: A complete Lean 4 theorem statement, e.g.:
                     "theorem foo : ∀ n : ℕ, n + 0 = n := by"

        Returns:
            The initial ProofState with all goals open.
            On parse error, returns a ProofState with error set.
        """
        ...

    async def step(
        self,
        state: ProofState,
        tactic: str,
    ) -> StepResult:
        """
        Apply a tactic to the given proof state and return the result.

        Args:
            state:  The current proof state. Used to restore the REPL
                    to the correct position before applying the tactic.
            tactic: The tactic string to apply, e.g. "simp" or "apply h".

        Returns:
            StepResult containing the new ProofState and timing info.
            Never raises — errors are captured in StepResult.next_state.error.
        """
        ...

    async def close(self) -> None:
        """
        Shut down the executor and release all resources.
        Terminates any running Lean subprocess workers.
        """
        ...
