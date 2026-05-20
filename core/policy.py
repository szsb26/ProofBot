"""
Abstract interface for the policy model (tactic generator).

The PolicyModel protocol defines the contract that every tactic generator
must satisfy. The search algorithm talks exclusively to this interface —
it never imports from policy/, lean/, or any specific implementation.

This is the most important abstraction boundary in the codebase.
"""

from __future__ import annotations
from dataclasses import dataclass
from typing import Protocol, runtime_checkable

from core.proof_state import ProofState


@dataclass(frozen=True)
class TacticCandidate:
    """
    A single tactic proposed by the policy, with an associated log probability.

    Attributes:
        tactic:   The tactic string to send to Lean, e.g. "simp" or "apply h".
        log_prob: Log probability assigned by the model. Higher = more confident.
                  Used as the prior P(s, a) in the UCB formula.
                  Set to 0.0 when log probs are unavailable (e.g. some APIs).
    """
    tactic: str
    log_prob: float = 0.0

    @property
    def prob(self) -> float:
        """Probability in [0, 1]. Convenience accessor for UCB computation."""
        import math
        return math.exp(self.log_prob)

    def __repr__(self) -> str:
        return f"TacticCandidate({self.tactic!r}, log_prob={self.log_prob:.3f})"


@runtime_checkable
class PolicyModel(Protocol):
    """
    Protocol that every tactic generator must satisfy.

    Implementations:
        policy/anthropic.py  -> AnthropicPolicy   (Phase 1-2, API-backed)
        policy/openai.py     -> OpenAIPolicy       (comparison baseline)
        policy/vllm.py       -> VLLMPolicy         (Phase 3+, local model)
        policy/mock.py       -> MockPolicy         (testing, no API calls)

    The search algorithm only ever calls get_tactics(). Everything else
    is an implementation detail hidden behind this interface.
    """

    async def get_tactics(
        self,
        state: ProofState,
        premises: list[str],
        k: int = 8,
    ) -> list[TacticCandidate]:
        """
        Generate k tactic candidates for the given proof state.

        Args:
            state:    The current proof state. Contains open goals + hypotheses.
            premises: Relevant mathlib lemma names from the retriever.
                      e.g. ["Nat.add_zero", "Nat.add_comm"]
            k:        Number of candidates to return. Caller may receive fewer
                      if the model cannot generate k distinct tactics.

        Returns:
            List of TacticCandidate, sorted by log_prob descending.
            Never returns an empty list — at minimum returns [TacticCandidate("simp")].
        """
        ...

    async def close(self) -> None:
        """
        Clean shutdown. Drain any queues, release connections, free GPU memory.
        Always called when the search session ends.
        """
        ...
