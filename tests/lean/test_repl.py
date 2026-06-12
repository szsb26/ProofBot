"""
Unit and integration tests for lean/repl.py.

TestParseGoalString          — fast, no Lean needed; tests the goal string parser
TestSubprocessExecutor       — slow, real Lean; tests a single executor end-to-end
TestProveParallelIntegration — slow, real Lean; tests k (BestFirstSearch,
                               SubprocessExecutor) pairs running concurrently
                               via prove_parallel on the same theorem
TestEndToEnd                 — slow, real Lean + real Anthropic API; tests the
                               full stack: AnthropicPolicy → BestFirstSearch →
                               SubprocessExecutor → lake exe repl
"""

import os
import pytest
import pytest_asyncio
import asyncio
from lean.repl import SubprocessExecutor, _parse_goal_string, LEAN_PROJECT_DIR
from core.proof_state import ProofState
from policy.mock import MockPolicy
from policy.anthropic import AnthropicPolicy
from value.heuristic import HeuristicValue
from search.best_first import BestFirstSearch, prove_parallel


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
        # k BestFirstSearch + k SubprocessExecutor pairs all attempt the same
        # theorem concurrently via prove_parallel. MockPolicy supplies tactics
        # so no LLM API calls are needed. Real Lean can close this theorem with
        # just "simp" in one step, so we only assert overall success.
        k = 3
        policy = MockPolicy(tactics=["simp", "ring", "omega", "intro n"])
        value = HeuristicValue()

        executors = [SubprocessExecutor() for _ in range(k)]
        await asyncio.gather(*[e.start() for e in executors])

        try:
            searches = [
                BestFirstSearch(policy=policy, executor=e, value=value)
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
        value = HeuristicValue()

        executors = [SubprocessExecutor() for _ in range(k)]
        await asyncio.gather(*[e.start() for e in executors])

        try:
            searches = [
                BestFirstSearch(policy=policy, executor=e, value=value)
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
@pytest.mark.asyncio
class TestEndToEnd:

    async def test_anthropic_proves_simple_theorem(self):
        # Full stack: AnthropicPolicy calls the real Claude API to generate
        # tactics, BestFirstSearch drives the search, SubprocessExecutor
        # verifies each tactic against a real lake exe repl process.
        policy = AnthropicPolicy()
        executor = SubprocessExecutor()
        await executor.start()
        try:
            search = BestFirstSearch(
                policy=policy,
                executor=executor,
                value=HeuristicValue(),
                k=8,
            )
            result = await search.prove(
                "theorem foo : ∀ n : Nat, n + 0 = n := by",
                budget=10,
            )
            assert result.success
            assert len(result.proof_trace) > 0
        finally:
            await executor.close()
            await policy.close()

    async def test_anthropic_prove_parallel(self):
        # k independent (AnthropicPolicy, BestFirstSearch, SubprocessExecutor)
        # triples run concurrently. The first to find a proof wins.
        k = 3
        policy = AnthropicPolicy()
        value = HeuristicValue()
        executors = [SubprocessExecutor() for _ in range(k)]
        await asyncio.gather(*[e.start() for e in executors])
        try:
            searches = [
                BestFirstSearch(policy=policy, executor=e, value=value, k=8)
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
            await policy.close()

    async def test_binomial_square(self):
        # Level 1: arithmetic identity over Int.
        # simp and omega won't close this — Claude must produce "ring".
        # ring checks that both sides of an algebraic equation are the same, by
        # expanding and simplifying. It uses a) distributivity, commutativity, and associativity 
        # of + and * to expand both sides to check the equality, hence ring.
        #
        # Expected proof: intro a b; ring
        policy = AnthropicPolicy()
        executor = SubprocessExecutor()
        await executor.start()
        try:
            search = BestFirstSearch(
                policy=policy,
                executor=executor,
                value=HeuristicValue(),
                k=8,
            )
            result = await search.prove(
                "theorem binomial_sq : ∀ a b : Int, (a + b)^2 = a^2 + 2*a*b + b^2 := by",
                budget=20,
            )
            assert result.success
            assert len(result.proof_trace) > 0
        finally:
            await executor.close()
            await policy.close()

    async def test_contrapositive(self):
        # Level 2: propositional logic — modus tollens / contrapositive.
        # Requires genuine multi-step reasoning: intro, apply, exact.
        # simp/omega/ring do not apply here.
        #
        # Expected proof: intro p q hpq hnq hp; exact hnq (hpq hp)
        policy = AnthropicPolicy()
        executor = SubprocessExecutor()
        await executor.start()
        try:
            search = BestFirstSearch(
                policy=policy,
                executor=executor,
                value=HeuristicValue(),
                k=8,
            )
            result = await search.prove(
                "theorem contrapositive : ∀ (p q : Prop), (p → q) → ¬q → ¬p := by",
                budget=20,
            )
            assert result.success
            assert len(result.proof_trace) > 0
        finally:
            await executor.close()
            await policy.close()
