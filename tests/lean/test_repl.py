"""
Integration tests for lean/repl.py
"""

import pytest
import pytest_asyncio
import asyncio
from pathlib import Path
from unittest.mock import AsyncMock, MagicMock, patch
from lean.repl import SubprocessExecutor, _parse_goal_string, LEAN_PROJECT_DIR
from core.executor import StepResult
from core.proof_state import ProofState, make_proof_state


# ---------------------------------------------------------------------------
# Parser tests (fast, no Lean needed)
# ---------------------------------------------------------------------------

class TestParseGoalString:

    def test_simple_goal(self):
        # A bare turnstile line with no hypotheses → one goal, no hypotheses
        result = _parse_goal_string("⊢ n + 0 = n")
        assert result.num_goals == 1
        assert result.goals[0].target == "n + 0 = n"
        assert len(result.goals[0].hypotheses) == 0

    def test_goal_with_hypotheses(self):
        # Lines before ⊢ are parsed as hypotheses; "name : type" format
        result = _parse_goal_string("n : Nat\nh : n > 0\n⊢ n + 0 = n")
        assert result.num_goals == 1
        assert result.goals[0].target == "n + 0 = n"
        assert len(result.goals[0].hypotheses) == 2
        assert result.goals[0].hypotheses[0].name == "n"
        assert result.goals[0].hypotheses[0].type_ == "Nat"
        assert result.goals[0].hypotheses[1].name == "h"
        assert result.goals[0].hypotheses[1].type_ == "n > 0"

    def test_empty_goal(self):
        # Empty string means the REPL returned no goals → proof is closed
        result = _parse_goal_string("")
        assert result.is_closed

    def test_universal_goal(self):
        # ∀ in the target must be preserved verbatim, not mistaken for a hypothesis
        result = _parse_goal_string("⊢ ∀ (n : Nat), n + 0 = n")
        assert result.goals[0].target == "∀ (n : Nat), n + 0 = n"


# ---------------------------------------------------------------------------
# Routing unit tests (fast, no Lean needed — LeanWorker is mocked)
# ---------------------------------------------------------------------------

def _mock_worker(reset_state: ProofState, step_result: StepResult | None = None) -> MagicMock:
    worker = MagicMock()
    worker.start = AsyncMock()
    worker.stop = AsyncMock()
    worker.reset = AsyncMock(return_value=(reset_state, 0))
    if step_result is not None:
        worker.step = AsyncMock(return_value=step_result)
    return worker


@pytest.mark.asyncio
class TestSubprocessExecutorRouting:

    async def test_reset_registers_state_to_router(self):
        # After reset(), the returned state's hash must be in the router
        # pointing to the worker that processed it (index 0 here)
        state = make_proof_state(["n + 0 = n"])
        w0 = _mock_worker(state)
        with patch("lean.repl.LeanWorker", side_effect=[w0]):
            executor = SubprocessExecutor(capacity=1)
            await executor.start()
            await executor.reset("theorem foo : n + 0 = n := by")
        assert state.stable_hash() in executor._router
        assert executor._router[state.stable_hash()] == 0

    async def test_step_routes_to_owning_worker(self):
        # With capacity=2, reset() goes to w0. step() must also go to w0,
        # not w1 — even though w1 is available. w1 has no REPL state for this proof.
        state = make_proof_state(["n + 0 = n"])
        next_state = make_proof_state(["n + 0 = n"], [[("n", "Nat")]], depth=1)
        step_result = StepResult(next_state=next_state, tactic="intro n")
        w0 = _mock_worker(state, step_result)
        w1 = _mock_worker(state)
        with patch("lean.repl.LeanWorker", side_effect=[w0, w1]):
            executor = SubprocessExecutor(capacity=2)
            await executor.start()
            await executor.reset("theorem foo : n + 0 = n := by")
            await executor.step(state, "intro n")
        w0.step.assert_called_once_with(state, "intro n")
        w1.step.assert_not_called()

    async def test_step_registers_new_state_to_same_worker(self):
        # The state produced by step() must be registered to the same worker
        # as its parent, so subsequent steps on it route correctly
        state = make_proof_state(["n + 0 = n"])
        next_state = make_proof_state(["n + 0 = n"], [[("n", "Nat")]], depth=1)
        step_result = StepResult(next_state=next_state, tactic="intro n")
        w0 = _mock_worker(state, step_result)
        w1 = _mock_worker(state)
        with patch("lean.repl.LeanWorker", side_effect=[w0, w1]):
            executor = SubprocessExecutor(capacity=2)
            await executor.start()
            await executor.reset("theorem foo : n + 0 = n := by")
            await executor.step(state, "intro n")
        assert executor._router.get(next_state.stable_hash()) == 0

    async def test_step_unknown_state_returns_error(self):
        # Calling step() with a state that was never produced by this executor
        # (not in the router) must return an error rather than routing arbitrarily
        state = make_proof_state(["n + 0 = n"])
        unknown = make_proof_state(["some other goal"])
        w0 = _mock_worker(state)
        with patch("lean.repl.LeanWorker", side_effect=[w0]):
            executor = SubprocessExecutor(capacity=1)
            await executor.start()
            await executor.reset("theorem foo : n + 0 = n := by")
            result = await executor.step(unknown, "simp")
        assert result.next_state.is_error

    async def test_reset_round_robins_across_workers(self):
        # Two consecutive resets go to different workers (0 then 1),
        # so parallel proof searches don't pile onto a single worker
        state0 = make_proof_state(["goal zero"])
        state1 = make_proof_state(["goal one"])
        w0 = _mock_worker(state0)
        w1 = _mock_worker(state1)
        with patch("lean.repl.LeanWorker", side_effect=[w0, w1]):
            executor = SubprocessExecutor(capacity=2)
            await executor.start()
            await executor.reset("theorem a := by")
            await executor.reset("theorem b := by")
        assert executor._router[state0.stable_hash()] == 0
        assert executor._router[state1.stable_hash()] == 1

    async def test_error_state_from_reset_not_registered(self):
        # If reset() returns an error (e.g. Lean parse failure), that error
        # state must not be added to the router — it has no valid REPL backing
        error_state = ProofState(goals=(), error="parse error")
        w0 = _mock_worker(error_state)
        with patch("lean.repl.LeanWorker", side_effect=[w0]):
            executor = SubprocessExecutor(capacity=1)
            await executor.start()
            await executor.reset("theorem bad")
        assert error_state.stable_hash() not in executor._router


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
        # reset() against a real REPL should return an open ProofState with one goal
        state = await executor.reset(
            "theorem foo : ∀ n : Nat, n + 0 = n := by"
        )
        assert isinstance(state, ProofState)
        assert not state.is_closed
        assert not state.is_error
        assert state.num_goals == 1

    async def test_step_intro(self, executor):
        # "intro n" on a ∀ goal strips the quantifier and exposes the body as a new goal
        state = await executor.reset(
            "theorem foo : ∀ n : Nat, n + 0 = n := by"
        )
        result = await executor.step(state, "intro n")
        assert result.success
        assert not result.proof_closed
        assert result.next_state.num_goals == 1
        assert "n + 0 = n" in result.next_state.goals[0].target

    async def test_step_simp_closes(self, executor):
        # "intro n" then "simp" is a complete proof — simp should close the last goal
        state = await executor.reset(
            "theorem foo : ∀ n : Nat, n + 0 = n := by"
        )
        r1 = await executor.step(state, "intro n")
        r2 = await executor.step(r1.next_state, "simp")
        assert r2.success
        assert r2.proof_closed

    async def test_step_failing_tactic(self, executor):
        # "ring" cannot close a ∀ goal directly — REPL should report an error
        state = await executor.reset(
            "theorem foo : ∀ n : Nat, n + 0 = n := by"
        )
        result = await executor.step(state, "ring")
        assert not result.success
        assert result.next_state.is_error

    async def test_full_proof_trace(self, executor):
        # tactic_trace must accumulate every tactic applied since reset()
        state = await executor.reset(
            "theorem foo : ∀ n : Nat, n + 0 = n := by"
        )
        r1 = await executor.step(state, "intro n")
        r2 = await executor.step(r1.next_state, "simp")
        assert r2.next_state.tactic_trace == ("intro n", "simp")

    async def test_elapsed_ms_recorded(self, executor):
        # Each StepResult must record how long the REPL took (used to detect hangs)
        state = await executor.reset(
            "theorem foo : ∀ n : Nat, n + 0 = n := by"
        )
        result = await executor.step(state, "intro n")
        assert result.elapsed_ms > 0


@pytest.mark.skipif(
    not LEAN_PROJECT_DIR.exists(),
    reason="lean_project not found"
)
@pytest.mark.asyncio
class TestSubprocessExecutorCapacity2:
    """Integration tests that specifically exercise multi-worker routing."""

    @pytest_asyncio.fixture
    async def executor(self):
        exec_ = SubprocessExecutor(capacity=2)
        await exec_.start()
        yield exec_
        await exec_.close()

    async def test_step_succeeds_after_reset(self, executor):
        # With capacity=2, reset() and step() may land on different workers
        # if routing is broken. This confirms the router directs step() to
        # the correct worker — the one whose REPL has the proof state cached.
        state = await executor.reset(
            "theorem foo : ∀ n : Nat, n + 0 = n := by"
        )
        result = await executor.step(state, "intro n")
        assert result.success

    async def test_multi_step_proof(self, executor):
        # A two-step proof requires two sequential steps, each depending on
        # the previous state. Verifies that child states are also routed correctly.
        state = await executor.reset(
            "theorem foo : ∀ n : Nat, n + 0 = n := by"
        )
        r1 = await executor.step(state, "intro n")
        r2 = await executor.step(r1.next_state, "simp")
        assert r2.proof_closed

    async def test_parallel_tactics_same_state(self, executor):
        # Simulates what BestFirstSearch does: verify k tactics concurrently
        # from the same state. Both calls go to the same worker (via the router)
        # and are serialized through its lock — one succeeds, one fails.
        state = await executor.reset(
            "theorem foo : ∀ n : Nat, n + 0 = n := by"
        )
        r1, r2 = await asyncio.gather(
            executor.step(state, "intro n"),
            executor.step(state, "ring"),
        )
        assert r1.success
        assert not r2.success
