"""
Unit and integration tests for lean/repl.py.

TestParseGoalString   — fast, no Lean needed; tests the goal string parser
TestSubprocessExecutor — slow, real Lean; tests the executor end-to-end
"""

import pytest
import pytest_asyncio
import asyncio
from lean.repl import SubprocessExecutor, _parse_goal_string, LEAN_PROJECT_DIR
from core.proof_state import ProofState


# ---------------------------------------------------------------------------
# Parser tests (fast, no Lean needed)
# ---------------------------------------------------------------------------

class TestParseGoalString:

    def test_simple_goal(self):
        # _parse_goal_string() returns a ProofState with a single Goal.
        # No hypotheses because the string has no " : " lines.
        result = _parse_goal_string("⊢ n + 0 = n")
        assert result.num_goals == 1
        assert result.goals[0].target == "n + 0 = n"
        assert len(result.goals[0].hypotheses) == 0

    def test_goal_with_hypotheses(self):
        # Lines before ⊢ are parsed as hypotheses in "name : type" format.
        result = _parse_goal_string("n : Nat\nh : n > 0\n⊢ n + 0 = n")
        assert result.num_goals == 1
        assert result.goals[0].target == "n + 0 = n"
        assert len(result.goals[0].hypotheses) == 2
        assert result.goals[0].hypotheses[0].name == "n"
        assert result.goals[0].hypotheses[0].type_ == "Nat"
        assert result.goals[0].hypotheses[1].name == "h"
        assert result.goals[0].hypotheses[1].type_ == "n > 0"

    def test_empty_goal(self):
        # Empty string means the REPL returned no goals → proof is closed.
        result = _parse_goal_string("")
        assert result.is_closed

    def test_universal_goal(self):
        # ∀ in the target must not be mistaken for a hypothesis even though
        # the string contains " : ".
        result = _parse_goal_string("⊢ ∀ (n : Nat), n + 0 = n")
        assert result.goals[0].target == "∀ (n : Nat), n + 0 = n"


# ---------------------------------------------------------------------------
# Integration tests (slow, real Lean)
# ---------------------------------------------------------------------------

@pytest.mark.skipif(
    not LEAN_PROJECT_DIR.exists(),
    reason="lean_project not found"
)
@pytest.mark.asyncio
class TestSubprocessExecutor:

    @pytest_asyncio.fixture
    async def executor(self):
        """Start one executor before each test, shut it down after."""
        exec_ = SubprocessExecutor()
        await exec_.start()
        yield exec_
        await exec_.close()

    async def test_reset_simple_theorem(self, executor):
        # reset() against a real REPL should return an open ProofState.
        state = await executor.reset(
            "theorem foo : ∀ n : Nat, n + 0 = n := by"
        )
        assert isinstance(state, ProofState)
        assert not state.is_closed
        assert not state.is_error
        assert state.num_goals == 1

    async def test_step_intro(self, executor):
        # "intro n" on a ∀ goal strips the quantifier and exposes the body.
        state = await executor.reset(
            "theorem foo : ∀ n : Nat, n + 0 = n := by"
        )
        result = await executor.step(state, "intro n")
        assert result.success
        assert not result.proof_closed
        assert result.next_state.num_goals == 1
        assert "n + 0 = n" in result.next_state.goals[0].target

    async def test_step_simp_closes(self, executor):
        # "intro n" then "simp" is a complete proof.
        state = await executor.reset(
            "theorem foo : ∀ n : Nat, n + 0 = n := by"
        )
        r1 = await executor.step(state, "intro n")
        r2 = await executor.step(r1.next_state, "simp")
        assert r2.success
        assert r2.proof_closed

    async def test_step_failing_tactic(self, executor):
        # "ring" cannot close a ∀ goal directly — REPL reports an error.
        state = await executor.reset(
            "theorem foo : ∀ n : Nat, n + 0 = n := by"
        )
        result = await executor.step(state, "ring")
        assert not result.success
        assert result.next_state.is_error

    async def test_full_proof_trace(self, executor):
        # tactic_trace must accumulate every tactic applied since reset().
        state = await executor.reset(
            "theorem foo : ∀ n : Nat, n + 0 = n := by"
        )
        r1 = await executor.step(state, "intro n")
        r2 = await executor.step(r1.next_state, "simp")
        assert r2.next_state.tactic_trace == ("intro n", "simp")

    async def test_elapsed_ms_recorded(self, executor):
        # Each StepResult must record how long the REPL took.
        state = await executor.reset(
            "theorem foo : ∀ n : Nat, n + 0 = n := by"
        )
        result = await executor.step(state, "intro n")
        assert result.elapsed_ms > 0

    async def test_two_executors_independent(self):
        # Two SubprocessExecutor instances each own their own REPL process.
        # They must be able to run concurrent proofs without interfering.
        exec0 = SubprocessExecutor()
        exec1 = SubprocessExecutor()
        await exec0.start()
        await exec1.start()
        try:
            s0, s1 = await asyncio.gather(
                exec0.reset("theorem foo : ∀ n : Nat, n + 0 = n := by"),
                exec1.reset("theorem foo : ∀ n : Nat, n + 0 = n := by"),
            )

            async def full_proof(executor, state):
                r1 = await executor.step(state, "intro n")
                r2 = await executor.step(r1.next_state, "simp")
                return r2.proof_closed

            closed0, closed1 = await asyncio.gather(
                full_proof(exec0, s0),
                full_proof(exec1, s1),
            )
            assert closed0
            assert closed1
        finally:
            await exec0.close()
            await exec1.close()
