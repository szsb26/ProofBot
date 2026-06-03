"""
Unit and integration tests for lean/repl.py.

TestParseGoalString      — fast, no Lean needed; tests the goal string parser
TestSubprocessExecutorRouting — fast, no Lean needed; tests worker routing logic
                               with mocked LeanWorkers
TestSubprocessExecutor   — slow, real Lean; tests a single worker end-to-end
TestSubprocessExecutorCapacity2 — slow, real Lean; tests concurrent multi-worker
                                   behavior including session isolation
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
        '''
        Test the _parse_goal_string() function
        '''
        # _parse_goal_string() returns a ProofState object with a single Goal. Note that in this goal, there is no hypotheses since our
        # string does not contain lines with ":". 
        result = _parse_goal_string("⊢ n + 0 = n")
        assert result.num_goals == 1
        assert result.goals[0].target == "n + 0 = n"
        assert len(result.goals[0].hypotheses) == 0

    def test_goal_with_hypotheses(self):
        '''
        Test the _parse_goal_string() function with nonempty hypotheses
        '''
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
        '''
        Test if ProofState.is_closed is correctly set when there are no more ProofState.goals left to prove, which means the proof is closed.
        Recall that ProofState.goals is a tuple of Goal objects.
        '''
        # Empty string means the REPL returned no goals → proof is closed
        result = _parse_goal_string("")
        assert result.is_closed

    def test_universal_goal(self):
        '''
        Test that universal quantifiers in the target are parsed correctly and not mistaken for hypotheses.
        In this example, the target is "∀ (n : Nat), n + 0 = n" and there are no hypotheses, even though there is a ": " in the string.
        The presence of "∀" at the start of the target should not interfere with parsing.
        '''
        # ∀ in the target must be preserved verbatim, not mistaken for a hypothesis
        result = _parse_goal_string("⊢ ∀ (n : Nat), n + 0 = n")
        assert result.goals[0].target == "∀ (n : Nat), n + 0 = n"


# ---------------------------------------------------------------------------
# Routing unit tests (fast, no Lean needed — LeanWorker is mocked)
# ---------------------------------------------------------------------------

def _mock_worker(reset_state: ProofState, step_result: StepResult | None = None) -> MagicMock:
    '''
    A mock LeanWorker for testing SubprocessExecutor routing logic without a real Lean process.
    start(), stop(), reset(), and step() must all be AsyncMock because SubprocessExecutor
    awaits each of them — a regular MagicMock would raise a TypeError when awaited.
    '''
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
        # After reset(), the returned state must have a non-empty session_id
        # and its (session_id, stable_hash) key must be in the router pointing
        # to the worker that processed it (index 0 here).
        base_state = make_proof_state(["n + 0 = n"])
        w0 = _mock_worker(base_state)
        # patch() replaces LeanWorker class with the mock worker class we defined above.
        # each instance/call to the real LeanWorker() constructor will instead return the instances
        # in side_effect in order. So first call to LeanWorker() returns w0, second call returns w1, and so on.
        with patch("lean.repl.LeanWorker", side_effect=[w0]):
            executor = SubprocessExecutor(capacity=1)
            await executor.start()
            state = await executor.reset("theorem foo : n + 0 = n := by")
        assert state.session_id != ""
        assert executor._router[(state.session_id, state.stable_hash())] == 0

    async def test_step_routes_to_owning_worker(self):
        # With capacity=2, reset() goes to w0. step() must also go to w0,
        # not w1 — even though w1 is available. w1 has no REPL state for this proof.
        base_state = make_proof_state(["n + 0 = n"])
        next_base = make_proof_state(["n + 0 = n"], [[("n", "Nat")]], depth=1)
        step_result = StepResult(next_state=next_base, tactic="intro n")
        w0 = _mock_worker(base_state, step_result)
        w1 = _mock_worker(base_state)
        with patch("lean.repl.LeanWorker", side_effect=[w0, w1]):
            executor = SubprocessExecutor(capacity=2)
            await executor.start()
            state = await executor.reset("theorem foo : n + 0 = n := by")
            await executor.step(state, "intro n")
        # state carries the session_id, so worker.step receives it
        w0.step.assert_called_once_with(state, "intro n")
        w1.step.assert_not_called()

    async def test_step_registers_new_state_to_same_worker(self):
        # The state produced by step() must be registered to the same worker
        # as its parent, so all subsequent steps route correctly down the branch.
        base_state = make_proof_state(["n + 0 = n"])
        next_base = make_proof_state(["n + 0 = n"], [[("n", "Nat")]], depth=1)
        step_result = StepResult(next_state=next_base, tactic="intro n")
        w0 = _mock_worker(base_state, step_result)
        w1 = _mock_worker(base_state)
        with patch("lean.repl.LeanWorker", side_effect=[w0, w1]):
            executor = SubprocessExecutor(capacity=2)
            await executor.start()
            state = await executor.reset("theorem foo : n + 0 = n := by")
            result = await executor.step(state, "intro n")
        assert executor._router.get((state.session_id, result.next_state.stable_hash())) == 0

    async def test_step_propagates_session_id(self):
        # session_id must be stamped onto every state returned by step() so
        # the router key stays consistent throughout the entire proof search.
        base_state = make_proof_state(["n + 0 = n"])
        next_base = make_proof_state(["n + 0 = n"], [[("n", "Nat")]], depth=1)
        step_result = StepResult(next_state=next_base, tactic="intro n")
        w0 = _mock_worker(base_state, step_result)
        with patch("lean.repl.LeanWorker", side_effect=[w0]):
            executor = SubprocessExecutor(capacity=1)
            await executor.start()
            state = await executor.reset("theorem foo : n + 0 = n := by")
            result = await executor.step(state, "intro n")
        assert result.next_state.session_id == state.session_id

    async def test_step_unknown_state_returns_error(self):
        # Calling step() with a state not in the router (no session_id set,
        # never produced by this executor) must return an error, not route arbitrarily.
        base_state = make_proof_state(["n + 0 = n"])
        unknown = make_proof_state(["some other goal"])  # session_id=""
        w0 = _mock_worker(base_state)
        with patch("lean.repl.LeanWorker", side_effect=[w0]):
            executor = SubprocessExecutor(capacity=1)
            await executor.start()
            await executor.reset("theorem foo : n + 0 = n := by")
            result = await executor.step(unknown, "simp")
        assert result.next_state.is_error

    async def test_reset_round_robins_across_workers(self):
        # Two consecutive resets go to different workers (0 then 1),
        # so parallel proof searches don't pile onto a single worker.
        state0 = make_proof_state(["goal zero"])
        state1 = make_proof_state(["goal one"])
        w0 = _mock_worker(state0)
        w1 = _mock_worker(state1)
        with patch("lean.repl.LeanWorker", side_effect=[w0, w1]):
            executor = SubprocessExecutor(capacity=2)
            await executor.start()
            s0 = await executor.reset("theorem a := by")
            s1 = await executor.reset("theorem b := by")
        assert executor._router[(s0.session_id, s0.stable_hash())] == 0
        assert executor._router[(s1.session_id, s1.stable_hash())] == 1

    async def test_two_sessions_same_theorem_no_collision(self):
        # Two resets of identical theorems produce the same initial proof state
        # content but must get different session_ids, giving separate router entries
        # that point to separate workers. This is the core session isolation guarantee.
        base_state = make_proof_state(["n + 0 = n"])
        w0 = _mock_worker(base_state)
        w1 = _mock_worker(base_state)
        with patch("lean.repl.LeanWorker", side_effect=[w0, w1]):
            executor = SubprocessExecutor(capacity=2)
            await executor.start()
            s0 = await executor.reset("theorem foo : n + 0 = n := by")
            s1 = await executor.reset("theorem foo : n + 0 = n := by")
        assert s0.session_id != s1.session_id
        assert executor._router[(s0.session_id, s0.stable_hash())] == 0
        assert executor._router[(s1.session_id, s1.stable_hash())] == 1
        assert len(executor._router) == 2

    async def test_error_state_from_reset_not_registered(self):
        # If reset() returns an error (e.g. Lean parse failure), that error
        # state must not be added to the router — it has no valid REPL backing.
        error_state = ProofState(goals=(), error="parse error")
        w0 = _mock_worker(error_state)
        with patch("lean.repl.LeanWorker", side_effect=[w0]):
            executor = SubprocessExecutor(capacity=1)
            await executor.start()
            await executor.reset("theorem bad")
        assert len(executor._router) == 0


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
        # and a non-empty session_id so subsequent step() calls route correctly
        state = await executor.reset(
            "theorem foo : ∀ n : Nat, n + 0 = n := by"
        )
        assert isinstance(state, ProofState)
        assert not state.is_closed
        assert not state.is_error
        assert state.num_goals == 1
        assert state.session_id != ""

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
        # With capacity=2, reset() assigns a session_id and routes to worker 0.
        # step() uses (session_id, stable_hash) to find the same worker, so
        # the REPL proof state is always found in its cache.
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

    async def test_two_sessions_same_theorem_independent(self, executor):
        # Two concurrent proof attempts on the same theorem each get their own
        # session_id and worker, so they never interfere with each other.
        s0, s1 = await asyncio.gather(
            executor.reset("theorem foo : ∀ n : Nat, n + 0 = n := by"),
            executor.reset("theorem foo : ∀ n : Nat, n + 0 = n := by"),
        )
        assert s0.session_id != s1.session_id
        r0, r1 = await asyncio.gather(
            executor.step(s0, "intro n"),
            executor.step(s1, "intro n"),
        )
        assert r0.success
        assert r1.success

    async def test_k_workers_all_complete_full_proof(self, executor):
        # Both workers must be able to drive a full multi-step proof to completion
        # concurrently. This is the core requirement for k-parallel proof search.
        s0, s1 = await asyncio.gather(
            executor.reset("theorem foo : ∀ n : Nat, n + 0 = n := by"),
            executor.reset("theorem foo : ∀ n : Nat, n + 0 = n := by"),
        )

        async def full_proof(state):
            r1 = await executor.step(state, "intro n")
            r2 = await executor.step(r1.next_state, "simp")
            return r2.proof_closed

        closed0, closed1 = await asyncio.gather(full_proof(s0), full_proof(s1))
        assert closed0
        assert closed1
