"""
Abstract interface for the policy model (the search's director).

The PolicyModel protocol defines the contract that every director must
satisfy. The search algorithm talks exclusively to this interface — it
never imports from policy/, lean/, or any specific implementation.

Each turn, LedgerSearch hands the whole Ledger to get_next_action() and
gets back a DirectorResponse: which open state to continue from, which
states to abandon, and the single tactic to try there. That tactic is then
sent to Lean via the executor.

This is the most important abstraction boundary in the codebase.
"""

from __future__ import annotations
from typing import TYPE_CHECKING, Protocol, runtime_checkable

if TYPE_CHECKING:
    # Imported for typing only: policy/base.py imports from core/, so a
    # real import here would invert the layering and cycle.
    from core.ledger import Ledger
    from policy.base import DirectorResponse


# @runtime_checkable allows us to use isinstance() to check if an object satisfies the PolicyModel protocol,
# even though it's not a concrete class. This is useful for testing and for ensuring that our policy implementations
# conform to the expected interface.
@runtime_checkable
class PolicyModel(Protocol):
    """
    Protocol that every director (for ex., LLM model) must satisfy.

    Implementations:
        policy/anthropic.py   -> AnthropicPolicy   (API-backed)
        policy/deepseek.py    -> DeepSeekPolicy    (API-backed)
        policy/claude_cli.py  -> ClaudeCLIPolicy   (shells out to the claude CLI)
        policy/mock.py        -> MockPolicy        (testing, no API calls)
        core/trace.py         -> TracingPolicy     (wraps any of the above)

    The search algorithm only ever calls get_next_action() and close().
    Everything else is an implementation detail hidden behind this interface.
    """

    async def get_next_action(
        self,
        theorem: str,
        ledger: "Ledger",
        premises: list[str],
    ) -> "DirectorResponse":
        """
        Choose where to continue the search and what single tactic to try.

        Args:
            theorem:  The Lean 4 theorem statement being proved, for context.
            ledger:   Every open proof state plus the full record of what has
                      already been tried against each one.
            premises: Relevant Mathlib lemma names from the retriever,
                      e.g. ["Nat.add_zero", "Nat.add_comm"].

        Returns:
            A DirectorResponse naming the chosen state, any states to
            abandon, one tactic, and the reasoning behind the choice.

        Must never raise: on any API or parse failure, fall back to
        continuing an arbitrary frontier state rather than propagating the
        error, so a single bad turn cannot end the search.
        """
        ...

    async def close(self) -> None:
        """
        Clean shutdown. Drain any queues, release connections, free GPU memory.
        Always called when the search session ends.
        """
        ...
