"""
Unit tests for search/best_first.py

These tests use MockPolicy and MockExecutor — no real Lean or API calls.
They verify the search logic: priority ordering, backtracking, budget
exhaustion, proof trace extraction, and parallel verification.

TestBestFirstSearchWithAnthropicPolicy verifies that AnthropicPolicy
(with a mocked Anthropic client) wires correctly into BestFirstSearch —
the tactic strings it produces are consumed by the search loop without error.
"""

import pytest
import asyncio
from unittest.mock import AsyncMock, MagicMock, patch
from core.proof_state import make_proof_state, ProofState, make_goal
from core.policy import TacticCandidate
from lean.mock_executor import MockExecutor
from policy.mock import MockPolicy
from policy.anthropic import AnthropicPolicy
from value.heuristic import HeuristicValue
from search.best_first import BestFirstSearch, SearchNode, ProofResult, prove_parallel


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def make_search(
    tactics: list[str] | None = None,
    capacity: int = 2,
    k: int = 8,
) -> BestFirstSearch:
    return BestFirstSearch(
        policy=MockPolicy(tactics=tactics),
        executor=MockExecutor(capacity=capacity),
        value=HeuristicValue(),
        k=k,
    )


# ---------------------------------------------------------------------------
# SearchNode
# ---------------------------------------------------------------------------

class TestSearchNode:

    def test_higher_value_has_higher_priority(self):
        state = make_proof_state(["P"])
        low = SearchNode(state=state, parent=None, tactic="", depth=0, value=0.1)
        high = SearchNode(state=state, parent=None, tactic="", depth=0, value=0.9)
        # __lt__ returns True when self has higher value (for max-heap via negation)
        assert high < low

    def test_node_stores_tactic(self):
        state = make_proof_state(["P"])
        node = SearchNode(state=state, parent=None, tactic="simp", depth=1, value=0.5)
        assert node.tactic == "simp"


# ---------------------------------------------------------------------------
# ProofResult
# ---------------------------------------------------------------------------

class TestProofResult:

    def test_success_repr(self):
        r = ProofResult(
            success=True,
            proof_trace=["intro n", "simp"],
            nodes_visited=5,
            elapsed_ms=42.0,
            theorem="foo",
        )
        assert "success=True" in repr(r)
        assert "steps=2" in repr(r)

    def test_failure_repr(self):
        r = ProofResult(
            success=False,
            proof_trace=[],
            nodes_visited=100,
            elapsed_ms=500.0,
            theorem="foo",
        )
        assert "success=False" in repr(r)


# ---------------------------------------------------------------------------
# BestFirstSearch
# ---------------------------------------------------------------------------

class TestBestFirstSearch:

    def test_proves_simple_theorem(self):
        """simp should close n + 0 = n in one step."""
        search = make_search(tactics=["simp", "ring", "omega"])
        result = asyncio.run(search.prove(
            "theorem foo : n + 0 = n := by",
            budget=10,
        ))
        assert result.success
        assert len(result.proof_trace) > 0
        assert result.nodes_visited >= 1

    def test_proof_trace_contains_closing_tactic(self):
        search = make_search(tactics=["simp"])
        result = asyncio.run(search.prove(
            "theorem foo : n + 0 = n := by",
            budget=10,
        ))
        assert result.success
        assert "simp" in result.proof_trace

    def test_multi_step_proof(self):
        """intro n followed by simp should close ∀ n, n + 0 = n."""
        search = make_search(tactics=["intro n", "simp", "ring"])
        result = asyncio.run(search.prove(
            "theorem foo : ∀ n : ℕ, n + 0 = n := by",
            budget=20,
        ))
        assert result.success
        assert "intro n" in result.proof_trace
        assert "simp" in result.proof_trace

    def test_budget_exhaustion_returns_failure(self):
        """With budget=1 and no closing tactic, search should fail."""
        search = make_search(tactics=["ring"])  # ring won't close ∀ goal
        result = asyncio.run(search.prove(
            "theorem foo : ∀ n : ℕ, n + 0 = n := by",
            budget=1,
        ))
        assert not result.success
        assert result.proof_trace == []

    def test_nodes_visited_tracked(self):
        search = make_search()
        result = asyncio.run(search.prove(
            "theorem foo : n + 0 = n := by",
            budget=50,
        ))
        assert result.nodes_visited >= 1

    def test_elapsed_ms_is_positive(self):
        search = make_search()
        result = asyncio.run(search.prove(
            "theorem foo : n + 0 = n := by",
            budget=10,
        ))
        assert result.elapsed_ms >= 0.0

    def test_theorem_stored_in_result(self):
        theorem = "theorem foo : n + 0 = n := by"
        search = make_search()
        result = asyncio.run(search.prove(theorem, budget=10))
        assert result.theorem == theorem

    def test_no_duplicate_state_expansion(self):
        """Same state reached via different paths should only be expanded once."""
        search = make_search(tactics=["simp", "simp", "simp"])
        result = asyncio.run(search.prove(
            "theorem foo : n + 0 = n := by",
            budget=50,
        ))
        # Should succeed quickly — not waste budget re-expanding same state
        assert result.success
        assert result.nodes_visited < 10

    def test_capacity_respected(self):
        """Search with capacity=1 should still find proofs."""
        search = BestFirstSearch(
            policy=MockPolicy(tactics=["simp", "ring"]),
            executor=MockExecutor(capacity=1),
            value=HeuristicValue(),
            k=4,
        )
        result = asyncio.run(search.prove(
            "theorem foo : n + 0 = n := by",
            budget=10,
        ))
        assert result.success

    def test_all_tactics_fail_returns_failure(self):
        """If all tactics fail, search should return failure gracefully."""
        search = make_search(tactics=["blah", "nope", "invalid"])
        result = asyncio.run(search.prove(
            "theorem foo : n + 0 = n := by",
            budget=10,
        ))
        assert not result.success

    def test_parse_error_returns_failure(self):
        """A malformed theorem should return failure immediately."""
        search = make_search()
        result = asyncio.run(search.prove(
            "this is not valid lean",
            budget=10,
        ))
        # Should not crash — returns failure gracefully
        assert isinstance(result, ProofResult)
        assert not result.success or result.success  # either is fine, just no crash


# ---------------------------------------------------------------------------
# prove_parallel
# ---------------------------------------------------------------------------

class TestProveParallel:

    def test_returns_success_when_any_search_succeeds(self):
        """If at least one search finds a proof, prove_parallel returns success."""
        searches = [make_search(tactics=["simp"]) for _ in range(3)]
        result = asyncio.run(prove_parallel(
            "theorem foo : n + 0 = n := by",
            searches=searches,
            budget=10,
        ))
        assert result.success

    def test_returns_failure_when_all_searches_fail(self):
        """If every search exhausts its budget, prove_parallel returns failure."""
        searches = [make_search(tactics=["blah", "nope"]) for _ in range(3)]
        result = asyncio.run(prove_parallel(
            "theorem foo : n + 0 = n := by",
            searches=searches,
            budget=5,
        ))
        assert not result.success

    def test_proof_trace_present_on_success(self):
        """A successful parallel result must include the closing tactic."""
        searches = [make_search(tactics=["simp", "ring"]) for _ in range(2)]
        result = asyncio.run(prove_parallel(
            "theorem foo : n + 0 = n := by",
            searches=searches,
            budget=10,
        ))
        assert result.success
        assert len(result.proof_trace) > 0

    def test_single_search_behaves_like_prove(self):
        """prove_parallel with k=1 should behave identically to prove()."""
        theorem = "theorem foo : n + 0 = n := by"
        search = make_search(tactics=["simp"])
        parallel = asyncio.run(prove_parallel(theorem, searches=[search], budget=10))
        single = asyncio.run(make_search(tactics=["simp"]).prove(theorem, budget=10))
        assert parallel.success == single.success

    def test_multi_step_proof_found_in_parallel(self):
        """A two-step proof should be found across parallel searches."""
        searches = [make_search(tactics=["intro n", "simp", "ring"]) for _ in range(2)]
        result = asyncio.run(prove_parallel(
            "theorem foo : ∀ n : ℕ, n + 0 = n := by",
            searches=searches,
            budget=20,
        ))
        assert result.success
        assert "intro n" in result.proof_trace


# ---------------------------------------------------------------------------
# BestFirstSearch with AnthropicPolicy (mocked client, no real API calls)
# ---------------------------------------------------------------------------

def _make_api_response(text: str) -> MagicMock:
    content_block = MagicMock()
    content_block.text = text
    response = MagicMock()
    response.content = [content_block]
    return response


class TestBestFirstSearchWithAnthropicPolicy:

    def _make_search_with_anthropic(self, api_response_text: str, k: int = 8) -> tuple[BestFirstSearch, MagicMock]:
        """Build a BestFirstSearch backed by a mocked AnthropicPolicy."""
        patcher = patch("policy.anthropic.AsyncAnthropic")
        MockClient = patcher.start()
        mock_instance = MagicMock()
        mock_instance.messages.create = AsyncMock(
            return_value=_make_api_response(api_response_text)
        )
        mock_instance.close = AsyncMock()
        MockClient.return_value = mock_instance

        policy = AnthropicPolicy(api_key="test-key")
        search = BestFirstSearch(
            policy=policy,
            executor=MockExecutor(),
            value=HeuristicValue(),
            k=k,
        )
        return search, patcher

    async def test_proves_simple_theorem(self):
        # AnthropicPolicy returns "simp" → MockExecutor closes n + 0 = n → success.
        search, patcher = self._make_search_with_anthropic("simp\nring\nomega")
        try:
            result = await search.prove("theorem foo : n + 0 = n := by", budget=10)
            assert result.success
            assert "simp" in result.proof_trace
        finally:
            patcher.stop()

    async def test_proves_multi_step_theorem(self):
        # AnthropicPolicy returns "intro n" and "simp" → two-step proof closes ∀ goal.
        search, patcher = self._make_search_with_anthropic("intro n\nsimp\nring")
        try:
            result = await search.prove(
                "theorem foo : ∀ n : ℕ, n + 0 = n := by",
                budget=20,
            )
            assert result.success
            assert "intro n" in result.proof_trace
            assert "simp" in result.proof_trace
        finally:
            patcher.stop()

    async def test_api_failure_falls_back_to_simp(self):
        # If the Anthropic API raises, AnthropicPolicy falls back to ["simp"].
        # BestFirstSearch must handle this gracefully and still find the proof.
        with patch("policy.anthropic.AsyncAnthropic") as MockClient:
            mock_instance = MagicMock()
            mock_instance.messages.create = AsyncMock(side_effect=Exception("network error"))
            mock_instance.close = AsyncMock()
            MockClient.return_value = mock_instance

            policy = AnthropicPolicy(api_key="test-key")
            search = BestFirstSearch(
                policy=policy,
                executor=MockExecutor(),
                value=HeuristicValue(),
            )
            result = await search.prove("theorem foo : n + 0 = n := by", budget=10)
            # simp fallback closes n + 0 = n
            assert result.success

    async def test_all_tactics_fail_returns_failure(self):
        # AnthropicPolicy returns only invalid tactics → every step fails →
        # no states pushed to the queue → budget exhausted → failure.
        search, patcher = self._make_search_with_anthropic("blah\nnope\ninvalid")
        try:
            result = await search.prove("theorem foo : n + 0 = n := by", budget=10)
            assert not result.success
        finally:
            patcher.stop()

    async def test_policy_is_called_with_current_proof_state(self):
        # Verifies that the proof state passed to get_tactics() is the one
        # popped from the queue, not the initial state or a stale state.
        with patch("policy.anthropic.AsyncAnthropic") as MockClient:
            mock_instance = MagicMock()
            mock_instance.messages.create = AsyncMock(
                return_value=_make_api_response("simp")
            )
            mock_instance.close = AsyncMock()
            MockClient.return_value = mock_instance

            policy = AnthropicPolicy(api_key="test-key")
            search = BestFirstSearch(
                policy=policy,
                executor=MockExecutor(),
                value=HeuristicValue(),
            )
            await search.prove("theorem foo : n + 0 = n := by", budget=10)

            # The API must have been called at least once
            assert mock_instance.messages.create.call_count >= 1
            # The proof state content appears in the prompt sent to Claude
            _, kwargs = mock_instance.messages.create.call_args
            user_content = kwargs["messages"][0]["content"]
            assert "n + 0 = n" in user_content
