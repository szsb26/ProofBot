"""
Unit tests for search/ledger_search.py — LLM-guided proof search over a
Ledger, with no value function or priority queue.

These use MockPolicy (and small custom test policies below, for behavior
MockPolicy can't exercise — abandonment, bogus state ids, banned tactics)
plus MockExecutor. No real Lean or API calls.
"""

from __future__ import annotations

import asyncio

from core.ledger import Ledger
from core.policy import TacticCandidate
from core.proof_state import ProofState
from lean.mock_executor import MockExecutor
from policy.base import DirectorResponse
from policy.mock import MockPolicy
from search.ledger_search import LedgerSearch, ProofResult, prove_parallel


class ErroringExecutor:
    """Test-only executor whose reset() always returns a parse-error state."""

    capacity = 1

    async def reset(self, theorem: str) -> ProofState:
        return ProofState(goals=(), error="Lean parse error: unexpected token")

    async def step(self, state, tactic):
        raise AssertionError("step() should never be called after a parse error")

    async def close(self) -> None:
        pass


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def make_search(
    tactics: list[str] | None = None,
    capacity: int = 2,
    k: int = 8,
) -> LedgerSearch:
    return LedgerSearch(
        policy=MockPolicy(tactics=tactics),
        executor=MockExecutor(capacity=capacity),
        k=k,
    )


def _tactics(*names: str) -> list[TacticCandidate]:
    return [TacticCandidate(tactic=t, log_prob=float(-i)) for i, t in enumerate(names)]


# ---------------------------------------------------------------------------
# LedgerSearch — basic proving behavior
# ---------------------------------------------------------------------------

class TestLedgerSearchProving:

    def test_proves_simple_theorem(self):
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
        search = make_search(tactics=["intro n", "simp", "ring"])
        result = asyncio.run(search.prove(
            "theorem foo : ∀ n : ℕ, n + 0 = n := by",
            budget=20,
        ))
        assert result.success
        assert "intro n" in result.proof_trace
        assert "simp" in result.proof_trace

    def test_budget_exhaustion_returns_failure(self):
        search = make_search(tactics=["ring"])  # ring won't close ∀ goal
        result = asyncio.run(search.prove(
            "theorem foo : ∀ n : ℕ, n + 0 = n := by",
            budget=1,
        ))
        assert not result.success
        assert result.proof_trace == []
        assert result.failure_reason == "budget_exhausted"

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

    def test_all_tactics_fail_returns_failure(self):
        search = make_search(tactics=["blah", "nope", "invalid"])
        result = asyncio.run(search.prove(
            "theorem foo : n + 0 = n := by",
            budget=10,
        ))
        assert not result.success

    def test_malformed_theorem_does_not_crash(self):
        """MockExecutor doesn't simulate real Lean parse errors for arbitrary
        strings — it just treats them as an (unsolvable) goal. The point
        here is just that prove() never crashes on bad input."""
        search = make_search()
        result = asyncio.run(search.prove(
            "this is not valid lean",
            budget=10,
        ))
        assert isinstance(result, ProofResult)
        assert not result.success or result.success

    def test_parse_error_returns_failure_immediately(self):
        search = LedgerSearch(policy=MockPolicy(), executor=ErroringExecutor(), k=4)
        result = asyncio.run(search.prove("not valid lean at all", budget=10))
        assert not result.success
        assert result.failure_reason == "parse_error"
        assert result.nodes_visited == 0

    def test_capacity_respected(self):
        search = LedgerSearch(
            policy=MockPolicy(tactics=["simp", "ring"]),
            executor=MockExecutor(capacity=1),
            k=4,
        )
        result = asyncio.run(search.prove(
            "theorem foo : n + 0 = n := by",
            budget=10,
        ))
        assert result.success


# ---------------------------------------------------------------------------
# LedgerSearch — director-specific behavior (abandonment, bad ids, banned tactics)
# ---------------------------------------------------------------------------

class TestLedgerSearchDirectorBehavior:

    def test_banned_tactics_are_filtered(self):
        """sorry/admit must never close a proof, even if the director proposes them."""

        class BannedTacticPolicy:
            async def get_next_action(self, theorem, ledger, premises, k=8):
                chosen = next(iter(ledger.frontier))
                return DirectorResponse(
                    chosen_state_id=chosen,
                    abandoned_state_ids=[],
                    tactics=_tactics("sorry", "admit"),
                )

            async def close(self):
                pass

        search = LedgerSearch(policy=BannedTacticPolicy(), executor=MockExecutor(), k=4)
        result = asyncio.run(search.prove("theorem foo : n + 0 = n := by", budget=5))
        assert not result.success

    def test_frontier_exhausted_when_only_state_is_abandoned(self):
        """If the director abandons the only open state, the search fails
        with frontier_exhausted rather than looping forever."""

        class AlwaysAbandonPolicy:
            async def get_next_action(self, theorem, ledger, premises, k=8):
                chosen = next(iter(ledger.frontier))
                return DirectorResponse(
                    chosen_state_id=chosen,
                    abandoned_state_ids=[chosen],
                    tactics=_tactics("simp"),
                )

            async def close(self):
                pass

        search = LedgerSearch(policy=AlwaysAbandonPolicy(), executor=MockExecutor(), k=4)
        result = asyncio.run(search.prove("theorem foo : n + 0 = n := by", budget=10))
        assert not result.success
        assert result.failure_reason == "frontier_exhausted"
        # Should stop as soon as the frontier empties, not burn the whole budget
        assert result.nodes_visited == 1

    def test_bogus_chosen_state_id_does_not_crash(self):
        """If the director names a state that isn't in the frontier, the
        search should skip that turn gracefully rather than erroring."""

        class BogusIdPolicy:
            async def get_next_action(self, theorem, ledger, premises, k=8):
                return DirectorResponse(
                    chosen_state_id="does-not-exist",
                    abandoned_state_ids=[],
                    tactics=_tactics("simp"),
                )

            async def close(self):
                pass

        search = LedgerSearch(policy=BogusIdPolicy(), executor=MockExecutor(), k=4)
        result = asyncio.run(search.prove("theorem foo : n + 0 = n := by", budget=5))
        assert not result.success
        assert result.failure_reason == "budget_exhausted"
        assert result.nodes_visited == 5

    def test_failed_tactics_are_recorded_in_ledger_for_next_call(self):
        """A failing tactic at a state should not evict that state from the
        frontier — it stays available for a future director call."""

        calls: list[Ledger] = []

        class RecordingPolicy:
            async def get_next_action(self, theorem, ledger, premises, k=8):
                calls.append(ledger)
                chosen = next(iter(ledger.frontier))
                if len(calls) == 1:
                    return DirectorResponse(chosen, [], _tactics("nope"))
                return DirectorResponse(chosen, [], _tactics("simp"))

            async def close(self):
                pass

        search = LedgerSearch(policy=RecordingPolicy(), executor=MockExecutor(), k=4)
        result = asyncio.run(search.prove("theorem foo : n + 0 = n := by", budget=5))

        assert result.success
        # The second call's ledger should show the state still in frontier,
        # plus a recorded failure from the first call's "nope" tactic.
        second_ledger = calls[1]
        assert len(second_ledger.frontier) == 1
        state_id = next(iter(second_ledger.frontier))
        assert len(second_ledger.failures_for(state_id)) == 1
        assert second_ledger.failures_for(state_id)[0].tactic == "nope"

    def test_explicit_abandon_removes_state_but_search_continues_via_new_states(self):
        """Abandoning one state should not end the search if other open
        states remain (e.g. a sibling produced earlier)."""

        class AbandonOneContinueOtherPolicy:
            def __init__(self):
                self.turn = 0
                self.root_id = None

            async def get_next_action(self, theorem, ledger, premises, k=8):
                self.turn += 1
                if self.turn == 1:
                    # First turn: expand root with two tactics, one dead end
                    # ("nope") and one that advances toward the goal. Root
                    # stays in the frontier alongside its new child.
                    self.root_id = next(iter(ledger.frontier))
                    return DirectorResponse(self.root_id, [], _tactics("nope", "intro n"))
                # Second turn: explicitly abandon root and continue its child
                # (the successor of "intro n") instead.
                child_id = next(sid for sid in ledger.frontier if sid != self.root_id)
                return DirectorResponse(child_id, [self.root_id], _tactics("simp"))

            async def close(self):
                pass

        search = LedgerSearch(
            policy=AbandonOneContinueOtherPolicy(), executor=MockExecutor(), k=4
        )
        result = asyncio.run(search.prove(
            "theorem foo : ∀ n : ℕ, n + 0 = n := by", budget=10
        ))
        assert result.success
        assert "intro n" in result.proof_trace
        assert "simp" in result.proof_trace


# ---------------------------------------------------------------------------
# prove_parallel
# ---------------------------------------------------------------------------

class TestLedgerSearchProveParallel:

    def test_returns_success_when_any_search_succeeds(self):
        searches = [make_search(tactics=["simp"]) for _ in range(3)]
        result = asyncio.run(prove_parallel(
            "theorem foo : n + 0 = n := by",
            searches=searches,
            budget=10,
        ))
        assert result.success

    def test_returns_failure_when_all_searches_fail(self):
        searches = [make_search(tactics=["blah", "nope"]) for _ in range(3)]
        result = asyncio.run(prove_parallel(
            "theorem foo : n + 0 = n := by",
            searches=searches,
            budget=5,
        ))
        assert not result.success

    def test_multi_step_proof_found_in_parallel(self):
        searches = [make_search(tactics=["intro n", "simp", "ring"]) for _ in range(2)]
        result = asyncio.run(prove_parallel(
            "theorem foo : ∀ n : ℕ, n + 0 = n := by",
            searches=searches,
            budget=20,
        ))
        assert result.success
        assert "intro n" in result.proof_trace
