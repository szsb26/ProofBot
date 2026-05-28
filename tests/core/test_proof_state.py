"""
Unit tests for core/proof_state.py

Run with:  python3 -m pytest core/test_proof_state.py -v
"""

import pytest
from core.proof_state import (
    Hypothesis,
    Goal,
    ProofState,
    make_goal,
    make_proof_state,
)


# ---------------------------------------------------------------------------
# Hypothesis
# ---------------------------------------------------------------------------

class TestHypothesis:
    def test_serialize(self):
        h = Hypothesis(name="h", type_="n > 0")
        assert h.serialize() == "h : n > 0"

    def test_immutable(self):
        h = Hypothesis(name="h", type_="n > 0")
        with pytest.raises(Exception):
            h.name = "x"

    def test_equality(self):
        h1 = Hypothesis("h", "n > 0")
        h2 = Hypothesis("h", "n > 0")
        h3 = Hypothesis("h", "n > 1")
        assert h1 == h2
        assert h1 != h3


# ---------------------------------------------------------------------------
# Goal
# ---------------------------------------------------------------------------

class TestGoal:
    def test_serialize_no_hypotheses(self):
        goal = make_goal("n + 0 = n")
        assert goal.serialize() == "⊢ n + 0 = n"

    def test_serialize_with_hypotheses(self):
        goal = make_goal("n + 0 = n", [("n", "ℕ"), ("h", "n > 0")])
        result = goal.serialize()
        assert "n : ℕ" in result
        assert "h : n > 0" in result
        assert "⊢ n + 0 = n" in result

    def test_immutable(self):
        goal = make_goal("n + 0 = n")
        with pytest.raises(Exception):
            goal.target = "True"

    def test_equality(self):
        g1 = make_goal("n + 0 = n", [("n", "ℕ")])
        g2 = make_goal("n + 0 = n", [("n", "ℕ")])
        g3 = make_goal("n + 0 = n", [("m", "ℕ")])
        assert g1 == g2
        assert g1 != g3


# ---------------------------------------------------------------------------
# ProofState
# ---------------------------------------------------------------------------

class TestProofState:

    def test_open_state_not_closed(self):
        state = make_proof_state(["n + 0 = n"], [[("n", "ℕ")]])
        assert not state.is_closed
        assert not state.is_error
        assert state.num_goals == 1

    def test_closed_state(self):
        state = make_proof_state([])
        assert state.is_closed
        assert not state.is_error
        assert state.num_goals == 0

    def test_error_state(self):
        state = ProofState(goals=(), error="simp made no progress")
        assert state.is_error
        assert not state.is_closed  # error != closed

    def test_multi_goal_state(self):
        state = make_proof_state(
            ["P", "Q"],
            [[("h", "P ∨ Q")], [("h", "P ∨ Q")]]
        )
        assert state.num_goals == 2
        assert not state.is_closed

    def test_serialize_single_goal(self):
        state = make_proof_state(["n + 0 = n"], [[("n", "ℕ")]])
        result = state.serialize()
        assert "⊢ n + 0 = n" in result
        assert "n : ℕ" in result

    def test_serialize_multi_goal_shows_numbering(self):
        state = make_proof_state(["P", "Q"])
        result = state.serialize()
        assert "Goal 1/2" in result
        assert "Goal 2/2" in result

    def test_serialize_closed(self):
        state = make_proof_state([])
        assert state.serialize() == "[PROOF CLOSED]"

    def test_serialize_error(self):
        state = ProofState(goals=(), error="simp made no progress")
        result = state.serialize()
        assert "[ERROR]" in result
        assert "simp made no progress" in result

    def test_immutable(self):
        state = make_proof_state(["n + 0 = n"])
        with pytest.raises(Exception):
            state.depth = 5

    def test_depth_tracking(self):
        state = make_proof_state(["n + 0 = n"], depth=3)
        assert state.depth == 3

    def test_tactic_trace(self):
        state = ProofState(
            goals=make_proof_state(["n + 0 = n"]).goals,
            depth=2,
            tactic_trace=("intro n", "simp"),
        )
        assert state.tactic_trace == ("intro n", "simp")


# ---------------------------------------------------------------------------
# Hashing
# ---------------------------------------------------------------------------

class TestStableHash:

    def test_same_state_same_hash(self):
        s1 = make_proof_state(["n + 0 = n"], [[("n", "ℕ")]])
        s2 = make_proof_state(["n + 0 = n"], [[("n", "ℕ")]])
        assert s1.stable_hash() == s2.stable_hash()

    def test_different_target_different_hash(self):
        s1 = make_proof_state(["n + 0 = n"])
        s2 = make_proof_state(["n + 1 = n"])
        assert s1.stable_hash() != s2.stable_hash()

    def test_different_hypothesis_different_hash(self):
        s1 = make_proof_state(["n + 0 = n"], [[("n", "ℕ")]])
        s2 = make_proof_state(["n + 0 = n"], [[("m", "ℕ")]])
        assert s1.stable_hash() != s2.stable_hash()

    def test_depth_does_not_affect_hash(self):
        """Same logical state reached at different depths should hash identically."""
        s1 = make_proof_state(["n + 0 = n"], depth=1)
        s2 = make_proof_state(["n + 0 = n"], depth=5)
        assert s1.stable_hash() == s2.stable_hash()

    def test_tactic_trace_does_not_affect_hash(self):
        """Same goal reached via different tactics should hash identically."""
        s1 = ProofState(
            goals=make_proof_state(["n + 0 = n"]).goals,
            tactic_trace=("intro n",),
        )
        s2 = ProofState(
            goals=make_proof_state(["n + 0 = n"]).goals,
            tactic_trace=("intro n", "rw [Nat.add_zero]"),
        )
        assert s1.stable_hash() == s2.stable_hash()

    def test_hash_usable_as_dict_key(self):
        """Verify stable_hash output can be used to key a cache."""
        s1 = make_proof_state(["n + 0 = n"])
        cache = {s1.stable_hash(): "some_result"}
        s2 = make_proof_state(["n + 0 = n"])
        assert cache[s2.stable_hash()] == "some_result"

    def test_hash_is_short_string(self):
        s = make_proof_state(["n + 0 = n"])
        h = s.stable_hash()
        assert isinstance(h, str)
        assert len(h) == 16

    def test_session_id_does_not_affect_hash(self):
        """Two sessions on the same theorem have identical goal content but
        different session_ids. They must hash identically so the LeanWorker's
        internal proof state cache (keyed by stable_hash) can serve both."""
        s1 = ProofState(goals=make_proof_state(["n + 0 = n"]).goals, session_id="session-A")
        s2 = ProofState(goals=make_proof_state(["n + 0 = n"]).goals, session_id="session-B")
        assert s1.stable_hash() == s2.stable_hash()
