"""
Unit tests for lean/mock_executor.py
"""

import pytest
import asyncio
from core.proof_state import make_proof_state, make_goal, ProofState
from core.executor import StepResult, LeanExecutor
from lean.mock_executor import MockExecutor


class TestStepResult:

    def test_success(self):
        state = make_proof_state([])  # closed
        result = StepResult(next_state=state, tactic="simp")
        assert result.success
        assert result.proof_closed

    def test_error(self):
        state = ProofState(goals=(), error="simp failed")
        result = StepResult(next_state=state, tactic="simp")
        assert not result.success
        assert not result.proof_closed

    def test_open_success(self):
        state = make_proof_state(["Q"])
        result = StepResult(next_state=state, tactic="intro h")
        assert result.success
        assert not result.proof_closed


class TestMockExecutor:

    def test_satisfies_protocol(self):
        executor = MockExecutor()
        assert isinstance(executor, LeanExecutor)

    def test_capacity(self):
        assert MockExecutor(capacity=2).capacity == 2
        assert MockExecutor(capacity=10).capacity == 10

    def test_reset_returns_proof_state(self):
        executor = MockExecutor()
        state = asyncio.run(executor.reset("theorem foo : ∀ n : ℕ, n + 0 = n := by"))
        assert isinstance(state, ProofState)
        assert not state.is_closed
        assert state.num_goals == 1

    def test_simp_closes_add_zero(self):
        executor = MockExecutor()
        state = asyncio.run(executor.reset("theorem foo : n + 0 = n := by"))
        result = asyncio.run(executor.step(state, "simp"))
        assert result.success
        assert result.proof_closed

    def test_simp_fails_on_irrelevant_goal(self):
        executor = MockExecutor()
        state = ProofState(goals=(make_goal("P ∧ Q"),))
        result = asyncio.run(executor.step(state, "simp"))
        assert not result.success
        assert "no progress" in result.next_state.error

    def test_ring_closes_equation(self):
        executor = MockExecutor()
        state = ProofState(goals=(make_goal("a + b = b + a"),))
        result = asyncio.run(executor.step(state, "ring"))
        assert result.success
        assert result.proof_closed

    def test_sorry_always_closes(self):
        executor = MockExecutor()
        state = ProofState(goals=(make_goal("some impossible goal"),))
        result = asyncio.run(executor.step(state, "sorry"))
        assert result.success
        assert result.proof_closed

    def test_intro_strips_forall(self):
        executor = MockExecutor()
        state = ProofState(goals=(make_goal("∀ n : ℕ, n + 0 = n"),))
        result = asyncio.run(executor.step(state, "intro n"))
        assert result.success
        assert not result.proof_closed
        assert result.next_state.num_goals == 1
        assert "n + 0 = n" in result.next_state.goals[0].text

    def test_unknown_tactic_fails(self):
        executor = MockExecutor()
        state = ProofState(goals=(make_goal("n + 0 = n"),))
        result = asyncio.run(executor.step(state, "blahblah"))
        assert not result.success

    def test_depth_increments_on_success(self):
        executor = MockExecutor()
        state = ProofState(goals=(make_goal("∀ n : ℕ, n + 0 = n"),), depth=0)
        result = asyncio.run(executor.step(state, "intro n"))
        assert result.next_state.depth == 1

    def test_tactic_trace_accumulates(self):
        executor = MockExecutor()
        state = ProofState(goals=(make_goal("∀ n : ℕ, n + 0 = n"),))
        result1 = asyncio.run(executor.step(state, "intro n"))
        result2 = asyncio.run(executor.step(result1.next_state, "simp"))
        assert result2.next_state.tactic_trace == ("intro n", "simp")

    def test_elapsed_ms_is_set(self):
        executor = MockExecutor()
        state = ProofState(goals=(make_goal("n + 0 = n"),))
        result = asyncio.run(executor.step(state, "simp"))
        assert result.elapsed_ms >= 0.0

    def test_close_is_noop(self):
        executor = MockExecutor()
        asyncio.run(executor.close())
