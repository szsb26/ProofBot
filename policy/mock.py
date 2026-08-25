"""
Mock policy for testing the search loop without any API calls so we dont blow money on API calls.
Used mainly to debug the search infrastructure and ensure that the search loop correctly processes the tactics returned by the policy,
updates the proof state, and eventually finds a proof when given a fixed set of tactics that are known to solve the problem.

Cycles through a fixed list of tactics regardless of the proof state.
Useful for verifying that the search infrastructure works correctly
before plugging in a real LLM.
"""

from __future__ import annotations
from core.ledger import Ledger
from policy.base import DirectorResponse


class MockPolicy:
    """
    Proposes tactics from a fixed list, one per turn, ignoring the proof
    state entirely. Satisfies the PolicyModel protocol.
    """

    def __init__(self, tactics: list[str] | None = None):
        """
        Args:
            tactics: Fixed list of tactics to cycle through, one per
                     get_next_action() call. Defaults to a set of common
                     closing tactics.
        """
        self._tactics = tactics or [
            "simp",
            "ring",
            "omega",
            "tauto",
            "decide",
            "rfl",
            "norm_num",
            "linarith",
        ]
        self._turn = 0

    async def get_next_action(
        self,
        theorem: str,
        ledger: Ledger,
        premises: list[str],
    ) -> DirectorResponse:
        """
        Ignores theorem/premises. Always continues the most recently added
        open state (insertion order), proposing one tactic per call, cycling
        through the fixed tactic list turn over turn, and never abandons
        anything. Picking the newest state — rather than the first — lets a
        fixed-tactic search actually advance depth-first instead of
        re-trying an already-succeeded tactic at the root forever, since
        states are never auto-evicted from the frontier on success. Cycling
        one tactic per turn (rather than proposing several at once) mirrors
        how the real director now works: exactly one proposal per call.
        """
        chosen_id = next(reversed(ledger.frontier))
        tactic = self._tactics[self._turn % len(self._tactics)]
        self._turn += 1
        return DirectorResponse(
            chosen_state_id=chosen_id,
            abandoned_state_ids=[],
            tactic=tactic,
        )

    async def close(self) -> None:
        pass
