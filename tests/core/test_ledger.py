"""
Unit tests for core/ledger.py — the Ledger/LedgerEntry data structures that
replace the priority queue in the LLM-guided search redesign.
"""

from core.ledger import Ledger, LedgerEntry
from core.proof_state import make_proof_state


class TestLedgerAddState:

    def test_add_state_returns_stable_id(self):
        ledger = Ledger()
        state = make_proof_state(["n + 0 = n"])
        state_id = ledger.add_state(state)
        assert state_id == state.stable_hash()[:8]
        assert state_id in ledger.frontier
        assert ledger.frontier[state_id] is state

    def test_add_state_does_not_revive_abandoned_state(self):
        ledger = Ledger()
        state = make_proof_state(["n + 0 = n"])
        state_id = ledger.add_state(state)
        ledger.abandon([state_id])
        assert state_id not in ledger.frontier

        # Re-adding the same state should not put it back in the frontier
        ledger.add_state(state)
        assert state_id not in ledger.frontier

    def test_same_goal_different_path_shares_id(self):
        """Two states with identical goals hash identically regardless of path."""
        s1 = make_proof_state(["n + 0 = n"])
        s2 = make_proof_state(["n + 0 = n"])
        ledger = Ledger()
        id1 = ledger.add_state(s1)
        id2 = ledger.add_state(s2)
        assert id1 == id2


class TestLedgerRecording:

    def test_record_success_appends_entry(self):
        ledger = Ledger()
        ledger.record_success("abc123", "intro n", "def456")
        assert len(ledger.entries) == 1
        entry = ledger.entries[0]
        assert entry == LedgerEntry("abc123", "intro n", "success", "def456")

    def test_record_failure_appends_entry_with_no_child(self):
        ledger = Ledger()
        ledger.record_failure("abc123", "bad_tactic", "hallucinated_lemma")
        assert len(ledger.entries) == 1
        entry = ledger.entries[0]
        assert entry.outcome == "hallucinated_lemma"
        assert entry.child_id is None


class TestLedgerAbandon:

    def test_abandon_removes_from_frontier(self):
        ledger = Ledger()
        state = make_proof_state(["n + 0 = n"])
        state_id = ledger.add_state(state)
        ledger.abandon([state_id])
        assert state_id not in ledger.frontier
        assert state_id in ledger.abandoned

    def test_abandon_unknown_id_is_a_noop(self):
        ledger = Ledger()
        ledger.abandon(["never-existed"])
        assert "never-existed" in ledger.abandoned


class TestLedgerFailuresFor:

    def test_failures_for_filters_by_parent_and_excludes_success(self):
        ledger = Ledger()
        ledger.record_failure("a", "t1", "hallucinated_lemma")
        ledger.record_success("a", "t2", "b")
        ledger.record_failure("a", "t3", "type_mismatch")
        ledger.record_failure("other", "t4", "syntax_error")

        failures = ledger.failures_for("a")
        assert len(failures) == 2
        assert {f.tactic for f in failures} == {"t1", "t3"}

    def test_failures_for_empty_when_none_recorded(self):
        ledger = Ledger()
        assert ledger.failures_for("nonexistent") == []
