"""
Unit and integration tests for lean/repl.py.

TestParseGoalString          — fast, no Lean needed; tests the goal string parser
TestSubprocessExecutor       — slow, real Lean; tests a single executor end-to-end
TestProveParallelIntegration — slow, real Lean; tests k (LedgerSearch,
                               SubprocessExecutor) pairs running concurrently
                               via prove_parallel on the same theorem
TestEndToEnd                 — slow, real Lean + real Anthropic API; tests the
                               full stack: AnthropicPolicy → LedgerSearch →
                               SubprocessExecutor → lake exe repl
TestDeepSeekEndToEnd         — slow, real Lean + real DeepSeek API; same stack
                               with DeepSeekPolicy instead of AnthropicPolicy
"""

import os
import pytest
import pytest_asyncio
import asyncio
from unittest.mock import AsyncMock
from lean.repl import LeanWorker, SubprocessExecutor, _parse_goal_string, LEAN_PROJECT_DIR
from core.proof_state import ProofState, make_proof_state
from policy.mock import MockPolicy
from policy.anthropic import AnthropicPolicy
from policy.deepseek import DeepSeekPolicy
from search.ledger_search import LedgerSearch, _classify_tactic_error, prove_parallel


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
# LeanWorker.step() closure detection (fast, no real Lean — mocks _send)
# ---------------------------------------------------------------------------

class TestLeanWorkerStepClosureDetection:
    """
    Regression coverage for a real bug: apply?/exact? can report empty
    goals while proofStatus says "Incomplete: contains sorry" — no full
    match was found, so Lean fell back to a placeholder. The old condition
    `if not goals_raw or proof_status == "Completed":` treated empty goals
    ALONE as a genuine close, silently accepting these as full proofs. Only
    proofStatus == "Completed" may signal a genuine close now.

    No real Lean process needed — _send() is mocked with the exact raw
    response shapes captured from a live REPL session.
    """

    def _make_worker_with_cached_state(self):
        worker = LeanWorker(LEAN_PROJECT_DIR, load_mathlib=False)
        state = make_proof_state(["some goal"])
        worker._proof_state_cache[state.stable_hash()] = 0
        return worker, state

    async def test_completed_status_is_a_genuine_close(self):
        worker, state = self._make_worker_with_cached_state()
        worker._send = AsyncMock(return_value={
            "proofStatus": "Completed", "proofState": 1, "goals": [],
        })
        result = await worker.step(state, "simp")
        assert result.success
        assert result.proof_closed

    async def test_empty_goals_without_completed_status_is_not_a_close(self):
        """The apply?/exact? bug, reproduced from a real captured response."""
        worker, state = self._make_worker_with_cached_state()
        worker._send = AsyncMock(return_value={
            "proofStatus": "Incomplete: contains sorry",
            "proofState": 1,
            "goals": [],
            "messages": [
                {"severity": "info", "data": "Try this:\n  refine ?_"},
            ],
        })
        result = await worker.step(state, "apply?")
        assert not result.success
        assert not result.proof_closed
        assert "hidden sorry" in result.next_state.error.lower()

    async def test_empty_goals_without_completed_status_classified_as_hidden_sorry(self):
        worker, state = self._make_worker_with_cached_state()
        worker._send = AsyncMock(return_value={
            "proofStatus": "Incomplete: contains sorry",
            "proofState": 1,
            "goals": [],
        })
        result = await worker.step(state, "apply?")
        assert _classify_tactic_error(result.next_state.error) == "hidden_sorry"

    async def test_nonempty_goals_still_parsed_normally(self):
        """Sanity check: the fix must not disturb the ordinary
        'tactic succeeded, goals remain' path."""
        worker, state = self._make_worker_with_cached_state()
        worker._send = AsyncMock(return_value={
            "proofStatus": "",
            "proofState": 1,
            "goals": ["n : Nat\n⊢ n = n"],
        })
        result = await worker.step(state, "intro n")
        assert result.success
        assert not result.proof_closed
        assert result.next_state.goals[0].target == "n = n"


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
        exec_ = SubprocessExecutor(load_mathlib=False)
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
        # "ring" on a ∀ goal fails — Mathlib not loaded in this fixture
        # (load_mathlib=False for speed); even with Mathlib, ring requires
        # intro first. Either way the REPL reports an error.
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
        exec0 = SubprocessExecutor(load_mathlib=False)
        exec1 = SubprocessExecutor(load_mathlib=False)
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


# ---------------------------------------------------------------------------
# prove_parallel integration tests (slow, real Lean)
# ---------------------------------------------------------------------------

@pytest.mark.skipif(
    not LEAN_PROJECT_DIR.exists(),
    reason="lean_project not found"
)
@pytest.mark.asyncio
class TestProveParallelIntegration:

    async def test_k_searches_prove_same_theorem(self):
        # k LedgerSearch + k SubprocessExecutor pairs all attempt the same
        # theorem concurrently via prove_parallel. MockPolicy supplies tactics
        # so no LLM API calls are needed. Real Lean can close this theorem with
        # just "simp" in one step, so we only assert overall success.
        k = 3
        policy = MockPolicy(tactics=["simp", "ring", "omega", "intro n"])

        executors = [SubprocessExecutor(load_mathlib=False) for _ in range(k)]
        await asyncio.gather(*[e.start() for e in executors])

        try:
            searches = [
                LedgerSearch(policy=policy, executor=e)
                for e in executors
            ]
            result = await prove_parallel(
                "theorem foo : ∀ n : Nat, n + 0 = n := by",
                searches=searches,
                budget=50,
            )
            assert result.success
            assert len(result.proof_trace) > 0
        finally:
            for e in executors:
                await e.close()

    async def test_all_searches_fail_returns_failure(self):
        # All k searches fail because every tactic is invalid Lean syntax.
        # prove_parallel must return failure rather than crashing.
        k = 2
        policy = MockPolicy(tactics=["not_a_tactic", "also_invalid"])

        executors = [SubprocessExecutor(load_mathlib=False) for _ in range(k)]
        await asyncio.gather(*[e.start() for e in executors])

        try:
            searches = [
                LedgerSearch(policy=policy, executor=e)
                for e in executors
            ]
            result = await prove_parallel(
                "theorem foo : ∀ n : Nat, n + 0 = n := by",
                searches=searches,
                budget=10,
            )
            assert not result.success
        finally:
            for e in executors:
                await e.close()


# ---------------------------------------------------------------------------
# End-to-end tests (slow, real Lean + real Anthropic API)
# ---------------------------------------------------------------------------

@pytest.mark.skipif(
    not LEAN_PROJECT_DIR.exists(),
    reason="lean_project not found",
)
@pytest.mark.skipif(
    not os.environ.get("ANTHROPIC_API_KEY"),
    reason="ANTHROPIC_API_KEY not set",
)
@pytest.mark.asyncio(loop_scope="class")
class TestEndToEnd:
    # Mathlib loads once per class (shared_lean fixture).  The parallel test
    # still starts k=2 fresh executors — reusing the shared one there would risk
    # corrupting the REPL's stdout buffer if that search gets cancelled first.

    @pytest_asyncio.fixture(scope="class", loop_scope="class")
    async def shared_lean(self):
        """Start one Mathlib-loaded executor shared across all non-parallel tests."""
        policy = AnthropicPolicy()
        executor = SubprocessExecutor()
        await executor.start()
        yield policy, executor
        await executor.close()
        await policy.close()

    async def test_anthropic_proves_simple_theorem(self, shared_lean):
        policy, executor = shared_lean
        search = LedgerSearch(policy=policy, executor=executor, k=8)
        result = await search.prove("theorem foo : ∀ n : Nat, n + 0 = n := by", budget=10)
        assert result.success
        assert len(result.proof_trace) > 0

    async def test_anthropic_prove_parallel(self, shared_lean):
        # k independent searches run concurrently. Fresh executors so cancellation
        # can't corrupt the shared REPL's stdout buffer.
        policy, _ = shared_lean
        k = 2
        executors = [SubprocessExecutor() for _ in range(k)]
        await asyncio.gather(*[e.start() for e in executors])
        try:
            searches = [
                LedgerSearch(policy=policy, executor=e, k=8)
                for e in executors
            ]
            result = await prove_parallel(
                "theorem foo : ∀ n : Nat, n + 0 = n := by",
                searches=searches,
                budget=10,
            )
            assert result.success
            assert len(result.proof_trace) > 0
        finally:
            for e in executors:
                await e.close()

    async def test_binomial_square(self, shared_lean):
        # Level 1: algebraic identity over Int requiring a Mathlib tactic.
        # ring normalises both sides of a polynomial equation — it's only
        # available after LeanProject is imported (load_mathlib=True default).
        #
        # Expected proof: intro a b; ring
        policy, executor = shared_lean
        search = LedgerSearch(policy=policy, executor=executor, k=12)
        result = await search.prove(
            "theorem binomial_sq : ∀ a b : Int, (a + b)^2 = a^2 + 2*a*b + b^2 := by",
            budget=50,
        )
        assert result.success
        assert len(result.proof_trace) > 0

    async def test_contrapositive(self, shared_lean):
        # Level 2: propositional logic — modus tollens / contrapositive.
        # Requires genuine multi-step reasoning: intro, apply, exact.
        # simp/omega/ring do not apply here.
        #
        # Expected proof: intro p q hpq hnq hp; exact hnq (hpq hp)
        policy, executor = shared_lean
        search = LedgerSearch(policy=policy, executor=executor, k=8)
        result = await search.prove(
            "theorem contrapositive : ∀ (p q : Prop), (p → q) → ¬q → ¬p := by",
            budget=20,
        )
        assert result.success
        assert len(result.proof_trace) > 0


# ---------------------------------------------------------------------------
# End-to-end tests (slow, real Lean + real DeepSeek API)
# ---------------------------------------------------------------------------

@pytest.mark.skipif(
    not LEAN_PROJECT_DIR.exists(),
    reason="lean_project not found",
)
@pytest.mark.skipif(
    not os.environ.get("DEEPSEEK_API_KEY"),
    reason="DEEPSEEK_API_KEY not set",
)
@pytest.mark.asyncio(loop_scope="class")
class TestDeepSeekEndToEnd:
    # Mathlib loads once per class (shared_lean fixture). Same rationale as
    # TestEndToEnd — parallel test uses fresh executors to avoid cancellation issues.

    @pytest_asyncio.fixture(scope="class", loop_scope="class")
    async def shared_lean(self):
        """Start one Mathlib-loaded executor shared across all non-parallel tests."""
        policy = DeepSeekPolicy()
        executor = SubprocessExecutor()
        await executor.start()
        yield policy, executor
        await executor.close()
        await policy.close()

    async def test_deepseek_proves_simple_theorem(self, shared_lean):
        policy, executor = shared_lean
        search = LedgerSearch(policy=policy, executor=executor, k=8)
        result = await search.prove("theorem foo : ∀ n : Nat, n + 0 = n := by", budget=10)
        assert result.success
        assert len(result.proof_trace) > 0

    async def test_deepseek_prove_parallel(self, shared_lean):
        policy, _ = shared_lean
        k = 2
        executors = [SubprocessExecutor() for _ in range(k)]
        await asyncio.gather(*[e.start() for e in executors])
        try:
            searches = [
                LedgerSearch(policy=policy, executor=e, k=8)
                for e in executors
            ]
            result = await prove_parallel(
                "theorem foo : ∀ n : Nat, n + 0 = n := by",
                searches=searches,
                budget=10,
            )
            assert result.success
            assert len(result.proof_trace) > 0
        finally:
            for e in executors:
                await e.close()

    async def test_deepseek_add_comm(self, shared_lean):
        # Level 1: commutativity of natural number addition.
        # Requires intro n m then omega — tests that DeepSeek generates a
        # meaningful two-step proof for a non-trivial arithmetic theorem.
        #
        # Expected proof: intro n m; omega
        policy, executor = shared_lean
        search = LedgerSearch(policy=policy, executor=executor, k=8)
        result = await search.prove(
            "theorem add_comm_nat : ∀ n m : Nat, n + m = m + n := by",
            budget=20,
        )
        assert result.success
        assert len(result.proof_trace) > 0
