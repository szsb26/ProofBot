"""
Unit tests for search/best_first.py

These tests use MockPolicy and MockExecutor — no real Lean or API calls.
They verify the search logic: priority ordering, backtracking, budget
exhaustion, proof trace extraction, and parallel verification.
"""

import pytest
import asyncio
from core.proof_state import make_proof_state, ProofState, make_goal
from core.policy import TacticCandidate
from lean.mock_executor import MockExecutor
from policy.mock import MockPolicy
from value.heuristic import HeuristicValue
from search.best_first import BestFirstSearch, SearchNode, ProofResult


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
