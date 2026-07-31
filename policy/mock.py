"""
Mock policy for testing the search loop without any API calls so we dont blow money on API calls.
Used mainly to debug the MCTS search infrastructure and ensure that the search loop correctly processes the tactics returned by the policy, 
updates the proof state, and eventually finds a proof when given a fixed set of tactics that are known to solve the problem.

Returns a fixed list of tactics regardless of the proof state.
Useful for verifying that the search infrastructure works correctly
before plugging in a real LLM.
"""

from __future__ import annotations
from core.ledger import Ledger
from core.proof_state import ProofState
from core.policy import TacticCandidate
from policy.base import DirectorResponse


class MockPolicy:
    """
    Returns the same fixed tactics for every proof state.
    Satisfies the PolicyModel protocol.
    """

    def __init__(self, tactics: list[str] | None = None):
        """
        Args:
            tactics: Fixed list of tactics to always return.
                     Defaults to a set of common closing tactics.
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

    async def get_tactics(
        self,
        state: ProofState,
        premises: list[str],
        k: int = 8,
    ) -> list[TacticCandidate]:
        """
        Ignores the proof state and premises, always returns the same tactics. Recall that ProofState contains a list of open goals, and
        Goals contain the target and hypotheses, where hypotheses are the "given" facts we can use to solve the goal. In a real policy,
        we would use this information to condition our tactic generation, but in MockPolicy we just return a fixed list.
        """
        candidates = self._tactics[:k]
        # Assign descending log probs so simp is tried first
        n = len(candidates)
        return [
            TacticCandidate(tactic=t, log_prob=float(-i))
            for i, t in enumerate(candidates)
        ]

    async def get_next_action(
        self,
        theorem: str,
        ledger: Ledger,
        premises: list[str],
        k: int = 8,
    ) -> DirectorResponse:
        """
        Ignores theorem/premises. Always continues the most recently added
        open state (insertion order) with the same fixed tactic list, and
        never abandons anything. Picking the newest state — rather than the
        first — lets a fixed-tactic search actually advance depth-first
        instead of re-trying an already-succeeded tactic at the root forever,
        since states are never auto-evicted from the frontier on success.
        """
        chosen_id = next(reversed(ledger.frontier))
        candidates = self._tactics[:k]
        tactics = [
            TacticCandidate(tactic=t, log_prob=float(-i))
            for i, t in enumerate(candidates)
        ]
        return DirectorResponse(
            chosen_state_id=chosen_id,
            abandoned_state_ids=[],
            tactics=tactics,
        )

    async def close(self) -> None:
        pass
