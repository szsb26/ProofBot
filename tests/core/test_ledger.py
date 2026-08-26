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

    def test_abandon_immediately_removes_from_frontier(self):
        ledger = Ledger()
        state = make_proof_state(["n + 0 = n"])
        state_id = ledger.add_state(state)
        ledger.abandon([state_id])
        assert state_id not in ledger.frontier

    def test_add_state_re_registers_a_previously_abandoned_id(self):
        """
        A state's id depends only on its goals, not on how it was reached —
        so two independent tactic paths can legitimately converge on the
        same logical state. If one branch abandons it, that must not
        permanently block a later, unrelated branch from registering a
        freshly-verified success that happens to hash to the same id
        (regression test for the silent-discard bug: add_state used to
        return the id as if it succeeded while never actually inserting
        the state, losing real progress with no record of it anywhere).
        """
        ledger = Ledger()
        state = make_proof_state(["n + 0 = n"])
        state_id = ledger.add_state(state)
        ledger.abandon([state_id])
        assert state_id not in ledger.frontier

        # A different branch later re-derives the identical state.
        returned_id = ledger.add_state(state)
        assert returned_id == state_id
        assert state_id in ledger.frontier
        assert ledger.frontier[state_id] is state

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
        ledger.record_failure("abc123", "bad_tactic")
        assert len(ledger.entries) == 1
        entry = ledger.entries[0]
        assert entry.outcome == "failed"
        assert entry.child_id is None

    def test_record_failure_defaults_error_to_empty_string(self):
        ledger = Ledger()
        ledger.record_failure("abc123", "bad_tactic")
        assert ledger.entries[0].error == ""

    def test_record_failure_stores_raw_error_text(self):
        ledger = Ledger()
        ledger.record_failure(
            "abc123", "bad_tactic", "unknown identifier 'Finset.bad_lemma'",
        )
        assert ledger.entries[0].error == "unknown identifier 'Finset.bad_lemma'"


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
        ledger.record_failure("a", "t1")
        ledger.record_success("a", "t2", "b")
        ledger.record_failure("a", "t3")
        ledger.record_failure("other", "t4")

        failures = ledger.failures_for("a")
        assert len(failures) == 2
        assert {f.tactic for f in failures} == {"t1", "t3"}

    def test_failures_for_empty_when_none_recorded(self):
        ledger = Ledger()
        assert ledger.failures_for("nonexistent") == []


class TestLedgerReasoning:

    def test_set_reasoning_stores_text(self):
        ledger = Ledger()
        ledger.set_reasoning("abc123", "Trying to establish the base case via simp.")
        assert ledger.reasoning["abc123"] == "Trying to establish the base case via simp."

    def test_set_reasoning_blank_text_is_a_noop(self):
        ledger = Ledger()
        ledger.set_reasoning("abc123", "")
        assert "abc123" not in ledger.reasoning

    def test_set_reasoning_overwrites_previous_plan(self):
        ledger = Ledger()
        ledger.set_reasoning("abc123", "First plan.")
        ledger.set_reasoning("abc123", "Revised plan after failures.")
        assert ledger.reasoning["abc123"] == "Revised plan after failures."

    def test_reasoning_defaults_to_empty_dict(self):
        ledger = Ledger()
        assert ledger.reasoning == {}


class TestAbandonAndRestore:
    """
    Abandonment is reversible. The director prunes speculatively and often
    asks for a pruned branch back a turn or two later; before restore()
    existed, that request silently discarded the turn — measured at 24 of 50
    turns in one imo2005_q3 trial and 20 of 50 in an imo1968_tetrahedron one.
    """

    def test_abandon_retains_the_state_for_later_restore(self):
        ledger = Ledger()
        state = make_proof_state(["n = n"])
        sid = ledger.add_state(state)

        ledger.abandon([sid])
        assert sid not in ledger.frontier
        assert sid in ledger.retired

        restored = ledger.restore(sid)
        assert restored == state
        assert ledger.frontier[sid] == state
        assert sid not in ledger.retired
        assert sid not in ledger.abandoned

    def test_restore_returns_none_for_an_id_never_held(self):
        """The director can name a hallucinated or stale id; restore must
        report that rather than inventing a state."""
        ledger = Ledger()
        assert ledger.restore("deadbeef") is None

    def test_restore_is_idempotent_for_a_live_state(self):
        ledger = Ledger()
        sid = ledger.add_state(make_proof_state(["n = n"]))
        assert ledger.restore(sid) is None      # never abandoned, nothing retired
        assert sid in ledger.frontier           # ...and still open

    def test_rederiving_an_abandoned_state_supersedes_the_retired_copy(self):
        """A state id is a hash of goals only, so an unrelated branch can
        re-derive an abandoned id. The fresh entry must win, leaving no
        stale copy that a later abandon/restore cycle could resurrect."""
        ledger = Ledger()
        state = make_proof_state(["n = n"])
        sid = ledger.add_state(state)
        ledger.abandon([sid])
        assert sid in ledger.retired

        again = ledger.add_state(state)
        assert again == sid
        assert sid in ledger.frontier
        assert sid not in ledger.retired
        assert sid not in ledger.abandoned
