"""
Unit tests for core/policy.py
"""

import pytest
import asyncio
from core.policy import TacticCandidate, PolicyModel
from policy.mock import MockPolicy


class TestTacticCandidate:

    def test_basic_construction(self):
        t = TacticCandidate(tactic="simp", log_prob=-0.5)
        assert t.tactic == "simp"
        assert t.log_prob == -0.5

    def test_default_log_prob(self):
        t = TacticCandidate(tactic="ring")
        assert t.log_prob == 0.0

    def test_prob_property(self):
        import math
        t = TacticCandidate(tactic="simp", log_prob=0.0)
        assert abs(t.prob - 1.0) < 1e-9

        t2 = TacticCandidate(tactic="simp", log_prob=-1.0)
        assert abs(t2.prob - math.exp(-1.0)) < 1e-9

    def test_immutable(self):
        t = TacticCandidate(tactic="simp")
        with pytest.raises(Exception):
            t.tactic = "ring"

    def test_repr(self):
        t = TacticCandidate(tactic="simp", log_prob=-1.5)
        assert "simp" in repr(t)
        assert "log_prob" in repr(t)


class TestMockPolicy:

    def test_satisfies_protocol(self):
        policy = MockPolicy()
        assert isinstance(policy, PolicyModel)

    def test_returns_candidates(self):
        policy = MockPolicy()
        from core.proof_state import make_proof_state
        state = make_proof_state(["n + 0 = n"])
        candidates = asyncio.run(policy.get_tactics(state, premises=[], k=4))
        assert len(candidates) == 4
        assert all(isinstance(c, TacticCandidate) for c in candidates)

    def test_respects_k(self):
        policy = MockPolicy()
        from core.proof_state import make_proof_state
        state = make_proof_state(["n + 0 = n"])
        for k in [1, 3, 5]:
            candidates = asyncio.run(policy.get_tactics(state, premises=[], k=k))
            assert len(candidates) == k

    def test_sorted_by_log_prob_descending(self):
        policy = MockPolicy()
        from core.proof_state import make_proof_state
        state = make_proof_state(["n + 0 = n"])
        candidates = asyncio.run(policy.get_tactics(state, premises=[], k=4))
        probs = [c.log_prob for c in candidates]
        assert probs == sorted(probs, reverse=True)

    def test_custom_tactics(self):
        policy = MockPolicy(tactics=["exact h", "assumption"])
        from core.proof_state import make_proof_state
        state = make_proof_state(["n + 0 = n"])
        candidates = asyncio.run(policy.get_tactics(state, premises=[], k=2))
        tactics = [c.tactic for c in candidates]
        assert "exact h" in tactics
        assert "assumption" in tactics

    def test_close_is_noop(self):
        policy = MockPolicy()
        asyncio.run(policy.close())
