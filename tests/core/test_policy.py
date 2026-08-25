"""
Unit tests for core/policy.py
"""

import asyncio

from core.ledger import Ledger
from core.policy import PolicyModel
from core.proof_state import make_proof_state
from policy.base import DirectorResponse
from policy.mock import MockPolicy


class TestMockPolicy:

    def test_satisfies_protocol(self):
        policy = MockPolicy()
        assert isinstance(policy, PolicyModel)

    def test_returns_a_director_response(self):
        policy = MockPolicy()
        ledger = Ledger()
        state_id = ledger.add_state(make_proof_state(["n + 0 = n"]))

        resp = asyncio.run(policy.get_next_action("theorem foo := by", ledger, []))

        assert isinstance(resp, DirectorResponse)
        assert resp.chosen_state_id == state_id
        assert resp.tactic
        assert resp.abandoned_state_ids == []

    def test_cycles_through_tactics_one_per_call(self):
        """One tactic per turn, so the list is consumed across calls rather
        than returned all at once."""
        policy = MockPolicy(tactics=["intro n", "simp", "ring"])
        ledger = Ledger()
        ledger.add_state(make_proof_state(["n + 0 = n"]))

        seen = [
            asyncio.run(policy.get_next_action("theorem foo := by", ledger, [])).tactic
            for _ in range(3)
        ]
        assert seen == ["intro n", "simp", "ring"]

    def test_wraps_around_when_the_list_is_exhausted(self):
        policy = MockPolicy(tactics=["simp", "ring"])
        ledger = Ledger()
        ledger.add_state(make_proof_state(["n + 0 = n"]))

        seen = [
            asyncio.run(policy.get_next_action("theorem foo := by", ledger, [])).tactic
            for _ in range(4)
        ]
        assert seen == ["simp", "ring", "simp", "ring"]

    def test_chooses_the_most_recently_added_state(self):
        """Picking the newest state — rather than the first — lets a
        fixed-tactic search advance depth-first instead of re-trying an
        already-succeeded tactic at the root forever, since states are never
        auto-evicted from the frontier on success."""
        policy = MockPolicy()
        ledger = Ledger()
        ledger.add_state(make_proof_state(["first goal"]))
        newest = ledger.add_state(make_proof_state(["second goal"]))

        resp = asyncio.run(policy.get_next_action("theorem foo := by", ledger, []))
        assert resp.chosen_state_id == newest

    def test_close_is_noop(self):
        policy = MockPolicy()
        asyncio.run(policy.close())
