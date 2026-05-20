"""
Mock executor for testing the search loop without a running Lean process.

Simulates Lean's behavior with a small hardcoded set of rules:
    - "simp" closes any goal containing "+ 0"
    - "ring" closes any goal that looks like an equation
    - "sorry" always closes any goal (unsound but useful for testing)
    - "intro x" adds a hypothesis and strips a universal quantifier
    - everything else fails with a plausible error message

This is intentionally simple. The goal is not to simulate Lean accurately
but to give the search loop enough signal to exercise backtracking,
multi-goal handling, and proof trace logging.
"""

from __future__ import annotations
import asyncio
import time

from core.proof_state import ProofState, Goal, Hypothesis, make_proof_state
from core.executor import StepResult


class MockExecutor:
    """
    Simulates a Lean REPL for testing purposes.
    Satisfies the LeanExecutor protocol.
    """

    def __init__(self, capacity: int = 2, step_delay_ms: float = 0.0):
        """
        Args:
            capacity:      Number of concurrent step() calls to allow.
                           Mirrors what real hardware supports.
            step_delay_ms: Artificial delay per step, simulating REPL latency.
                           Set to e.g. 100.0 to stress-test async behavior.
        """
        self._capacity = capacity
        self._step_delay_ms = step_delay_ms

    @property
    def capacity(self) -> int:
        return self._capacity

    async def reset(self, theorem: str) -> ProofState:
        """Parse a trivial goal from the theorem string."""
        if asyncio.get_event_loop().is_running():
            await asyncio.sleep(self._step_delay_ms / 1000.0)

        # Extract the goal from a simple theorem statement
        # e.g. "theorem foo : ∀ n : ℕ, n + 0 = n := by"
        # -> goal target is "∀ n : ℕ, n + 0 = n"
        if ":=" in theorem:
            statement = theorem.split(":=")[0]
            if ":" in statement:
                # take everything after the first colon
                goal_str = statement.split(":", 1)[1].strip()
                goal_str = goal_str.replace("theorem", "").strip()
            else:
                goal_str = statement.strip()
        else:
            goal_str = theorem.strip()

        from core.proof_state import make_goal
        goal = make_goal(goal_str)
        return ProofState(goals=(goal,), depth=0)

    async def step(self, state: ProofState, tactic: str) -> StepResult:
        """Apply a tactic using simple pattern matching rules."""
        start = time.perf_counter()

        if self._step_delay_ms > 0:
            await asyncio.sleep(self._step_delay_ms / 1000.0)

        next_state = self._apply_tactic(state, tactic)
        elapsed = (time.perf_counter() - start) * 1000

        return StepResult(
            next_state=next_state,
            tactic=tactic,
            elapsed_ms=elapsed,
        )

    async def close(self) -> None:
        pass

    # ------------------------------------------------------------------
    # Internal tactic simulation
    # ------------------------------------------------------------------

    def _apply_tactic(self, state: ProofState, tactic: str) -> ProofState:
        if state.is_closed or state.is_error:
            return ProofState(
                goals=state.goals,
                error="no goals to solve",
                depth=state.depth,
                tactic_trace=state.tactic_trace,
            )

        tactic = tactic.strip()
        current_goal = state.goals[0]
        remaining_goals = state.goals[1:]
        target = current_goal.target

        # sorry always closes the current goal (unsound but useful)
        if tactic == "sorry":
            return self._advance(state, remaining_goals, tactic)

        # simp closes goals containing arithmetic simplifications
        if tactic == "simp":
            if "+ 0" in target or "0 +" in target or target.strip() == "True":
                return self._advance(state, remaining_goals, tactic)
            return self._error(state, "simp made no progress")

        # ring closes equation goals
        if tactic == "ring":
            if "=" in target:
                return self._advance(state, remaining_goals, tactic)
            return self._error(state, "ring failed, goal is not an equation")

        # omega closes linear arithmetic goals
        if tactic == "omega":
            if any(op in target for op in ["<", ">", "≤", "≥", "=", "+"]):
                return self._advance(state, remaining_goals, tactic)
            return self._error(state, "omega could not close goal")

        # rfl closes reflexivity goals
        if tactic == "rfl":
            parts = target.split("=")
            if len(parts) == 2 and parts[0].strip() == parts[1].strip():
                return self._advance(state, remaining_goals, tactic)
            return self._error(state, "rfl failed, sides not definitionally equal")

        # intro strips a universal quantifier and adds a hypothesis
        if tactic.startswith("intro"):
            parts = tactic.split()
            name = parts[1] if len(parts) > 1 else "x"
            if target.startswith("∀"):
                # strip the quantifier and add a hypothesis
                inner = target.split(",", 1)[-1].strip()
                new_hyp = Hypothesis(name=name, type_="ℕ")
                new_hyps = current_goal.hypotheses + (new_hyp,)
                new_goal = Goal(hypotheses=new_hyps, target=inner)
                new_goals = (new_goal,) + remaining_goals
                return ProofState(
                    goals=new_goals,
                    depth=state.depth + 1,
                    tactic_trace=state.tactic_trace + (tactic,),
                )
            return self._error(state, "intro failed, goal is not a forall")

        # exact closes if the hypothesis exists
        if tactic.startswith("exact") or tactic.startswith("assumption"):
            hyp_names = [h.name for h in current_goal.hypotheses]
            term = tactic.split()[-1] if len(tactic.split()) > 1 else ""
            if term in hyp_names or tactic == "assumption":
                return self._advance(state, remaining_goals, tactic)
            return self._error(state, f"unknown identifier '{term}'")

        # everything else fails
        return self._error(state, f"tactic '{tactic}' failed")

    def _advance(
        self,
        state: ProofState,
        remaining_goals: tuple[Goal, ...],
        tactic: str,
    ) -> ProofState:
        """Return a new state with the current goal removed."""
        return ProofState(
            goals=remaining_goals,
            depth=state.depth + 1,
            tactic_trace=state.tactic_trace + (tactic,),
        )

    def _error(self, state: ProofState, message: str) -> ProofState:
        """Return an error state."""
        return ProofState(
            goals=state.goals,
            error=message,
            depth=state.depth,
            tactic_trace=state.tactic_trace,
        )
