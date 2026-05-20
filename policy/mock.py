"""
Mock policy for testing the search loop without any API calls.

Returns a fixed list of tactics regardless of the proof state.
Useful for verifying that the search infrastructure works correctly
before plugging in a real LLM.
"""

from __future__ import annotations
from core.proof_state import ProofState
from core.policy import TacticCandidate


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
        candidates = self._tactics[:k]
        # Assign descending log probs so simp is tried first
        n = len(candidates)
        return [
            TacticCandidate(tactic=t, log_prob=float(-i))
            for i, t in enumerate(candidates)
        ]

    async def close(self) -> None:
        pass
