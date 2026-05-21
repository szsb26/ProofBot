"""
Integration tests for lean/repl.py
"""

import pytest
import pytest_asyncio
import asyncio
from pathlib import Path
from lean.repl import SubprocessExecutor, _parse_goal_string, LEAN_PROJECT_DIR
from core.proof_state import ProofState


# ---------------------------------------------------------------------------
# Parser tests (fast, no Lean needed)
# ---------------------------------------------------------------------------

class TestParseGoalString:

    def test_simple_goal(self):
        result = _parse_goal_string("⊢ n + 0 = n")
        assert result.num_goals == 1
        assert result.goals[0].target == "n + 0 = n"
        assert len(result.goals[0].hypotheses) == 0

    def test_goal_with_hypotheses(self):
        result = _parse_goal_string("n : Nat\nh : n > 0\n⊢ n + 0 = n")
        assert result.num_goals == 1
        assert result.goals[0].target == "n + 0 = n"
        assert len(result.goals[0].hypotheses) == 2
        assert result.goals[0].hypotheses[0].name == "n"
        assert result.goals[0].hypotheses[0].type_ == "Nat"
        assert result.goals[0].hypotheses[1].name == "h"
        assert result.goals[0].hypotheses[1].type_ == "n > 0"

    def test_empty_goal(self):
        result = _parse_goal_string("")
        assert result.is_closed

    def test_universal_goal(self):
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
        """Create and start an executor, shut it down after test."""
        exec_ = SubprocessExecutor(capacity=1)
        await exec_.start()
        yield exec_
        await exec_.close()

    async def test_reset_simple_theorem(self, executor):
        state = await executor.reset(
            "theorem foo : ∀ n : Nat, n + 0 = n := by"
        )
        assert isinstance(state, ProofState)
        assert not state.is_closed
        assert not state.is_error
        assert state.num_goals == 1

    async def test_step_intro(self, executor):
        state = await executor.reset(
            "theorem foo : ∀ n : Nat, n + 0 = n := by"
        )
        result = await executor.step(state, "intro n")
        assert result.success
        assert not result.proof_closed
        assert result.next_state.num_goals == 1
        assert "n + 0 = n" in result.next_state.goals[0].target

    async def test_step_simp_closes(self, executor):
        state = await executor.reset(
            "theorem foo : ∀ n : Nat, n + 0 = n := by"
        )
        r1 = await executor.step(state, "intro n")
        r2 = await executor.step(r1.next_state, "simp")
        assert r2.success
        assert r2.proof_closed

    async def test_step_failing_tactic(self, executor):
        state = await executor.reset(
            "theorem foo : ∀ n : Nat, n + 0 = n := by"
        )
        result = await executor.step(state, "ring")
        assert not result.success
        assert result.next_state.is_error

    async def test_full_proof_trace(self, executor):
        state = await executor.reset(
            "theorem foo : ∀ n : Nat, n + 0 = n := by"
        )
        r1 = await executor.step(state, "intro n")
        r2 = await executor.step(r1.next_state, "simp")
        assert r2.next_state.tactic_trace == ("intro n", "simp")

    async def test_elapsed_ms_recorded(self, executor):
        state = await executor.reset(
            "theorem foo : ∀ n : Nat, n + 0 = n := by"
        )
        result = await executor.step(state, "intro n")
        assert result.elapsed_ms > 0
