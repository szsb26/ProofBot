"""
Mock executor for testing the search loop without a running Lean process.

Simulates Lean's behavior with a small hardcoded set of rules:
    - "simp" closes any goal containing "+ 0" (but not ∀ goals)
    - "ring" closes equation goals that are not universally quantified
    - "sorry" always closes any goal
    - "intro x" strips a universal quantifier and adds a hypothesis
    - "omega" closes linear arithmetic goals
    - "rfl" closes reflexivity goals
    - "exact h" / "assumption" close if hypothesis exists
    - everything else fails
"""

from __future__ import annotations
import asyncio
import time

from core.proof_state import ProofState, Goal, make_goal
from core.executor import StepResult


# The mock reads goals it wrote itself, in a shape it defined, so these two
# lookups are safe in a way that parsing Lean's output never was: there is no
# external source of truth to drift from. Goal carries text only (see its
# docstring — reconstructing Lean's rendering from parts corrupted 24% of real
# goals), so these replace the old .target / .hypotheses fields.

def _target_of(goal: Goal) -> str:
    """The part after the turnstile."""
    _, sep, tail = goal.text.partition("\u22a2")
    return tail.strip() if sep else goal.text.strip()


def _hypothesis_lines(goal: Goal) -> list[str]:
    """The context lines, i.e. everything above the turnstile."""
    out = []
    for line in goal.text.split("\n"):
        if line.strip().startswith("\u22a2"):
            break
        if line.strip():
            out.append(line)
    return out


def _hypothesis_names(goal: Goal) -> list[str]:
    names = []
    for line in _hypothesis_lines(goal):
        head, sep, _ = line.partition(" : ")
        if sep:
            names.extend(head.split())
    return names


class MockExecutor:
    """
    Simulates a Lean REPL for testing purposes.
    Satisfies the LeanExecutor protocol.
    """

    def __init__(self, capacity: int = 2, step_delay_ms: float = 0.0):
        self._capacity = capacity
        self._step_delay_ms = step_delay_ms

    @property
    def capacity(self) -> int:
        return self._capacity

    async def reset(self, theorem: str, preamble: str = "") -> ProofState:
        if self._step_delay_ms > 0:
            await asyncio.sleep(self._step_delay_ms / 1000.0)

        if ":=" in theorem:
            statement = theorem.split(":=")[0]
            if ":" in statement:
                goal_str = statement.split(":", 1)[1].strip()
                goal_str = goal_str.replace("theorem", "").strip()
            else:
                goal_str = statement.strip()
        else:
            goal_str = theorem.strip()

        goal = make_goal(goal_str)
        return ProofState(goals=(goal,), depth=0)

    async def step(self, state: ProofState, tactic: str) -> StepResult:
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
        target = _target_of(current_goal)

        # sorry always closes
        if tactic == "sorry":
            return self._advance(state, remaining_goals, tactic)

        # simp closes arithmetic simplification goals (not quantified)
        if tactic == "simp":
            if target.startswith("∀"):
                return self._error(state, "simp made no progress")
            if "+ 0" in target or "0 +" in target or target == "True":
                return self._advance(state, remaining_goals, tactic)
            return self._error(state, "simp made no progress")

        # ring closes equation goals that are NOT universally quantified
        if tactic == "ring":
            if target.startswith("∀"):
                return self._error(state, "ring failed, goal is universally quantified")
            if "=" in target:
                return self._advance(state, remaining_goals, tactic)
            return self._error(state, "ring failed, goal is not an equation")

        # omega closes linear arithmetic goals (not quantified)
        if tactic == "omega":
            if target.startswith("∀"):
                return self._error(state, "omega failed, goal is universally quantified")
            if any(op in target for op in ["<", ">", "≤", "≥", "=", "+"]):
                return self._advance(state, remaining_goals, tactic)
            return self._error(state, "omega could not close goal")

        # rfl closes reflexivity
        if tactic == "rfl":
            parts = target.split("=")
            if len(parts) == 2 and parts[0].strip() == parts[1].strip():
                return self._advance(state, remaining_goals, tactic)
            return self._error(state, "rfl failed, sides not definitionally equal")

        # intro strips a universal quantifier
        if tactic.startswith("intro"):
            parts = tactic.split()
            name = parts[1] if len(parts) > 1 else "x"
            if target.startswith("∀"):
                inner = target.split(",", 1)[-1].strip()
                new_goal = Goal(text="\n".join(
                    _hypothesis_lines(current_goal)
                    + [f"{name} : ℕ", f"⊢ {inner}"]
                ))
                new_goals = (new_goal,) + remaining_goals
                return ProofState(
                    goals=new_goals,
                    depth=state.depth + 1,
                    tactic_trace=state.tactic_trace + (tactic,),
                )
            return self._error(state, "intro failed, goal is not a forall")

        # exact / assumption
        if tactic.startswith("exact") or tactic == "assumption":
            hyp_names = _hypothesis_names(current_goal)
            term = tactic.split()[-1] if len(tactic.split()) > 1 else ""
            if term in hyp_names or tactic == "assumption":
                return self._advance(state, remaining_goals, tactic)
            return self._error(state, f"unknown identifier '{term}'")

        return self._error(state, f"tactic '{tactic}' failed")

    def _advance(self, state, remaining_goals, tactic):
        return ProofState(
            goals=remaining_goals,
            depth=state.depth + 1,
            tactic_trace=state.tactic_trace + (tactic,),
        )

    def _error(self, state, message):
        return ProofState(
            goals=state.goals,
            error=message,
            depth=state.depth,
            tactic_trace=state.tactic_trace,
        )
