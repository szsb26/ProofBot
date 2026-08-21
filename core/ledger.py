"""
Ledger-based proof search state.

A Ledger is a plain record of every attempted tactic and its outcome — it
carries no scores or rankings. Deciding which state to expand next (and when
to give up on a branch) is done by the LLM itself, using the ledger as its
input, rather than by a hand-coded heuristic driving a priority queue.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from core.proof_state import ProofState


@dataclass
class LedgerEntry:
    """
    One attempted tactic and what Lean said about it.

    Attributes:
        parent_id: id of the state the tactic was tried against.
        tactic:    The tactic string sent to Lean.
        outcome:   "success", or an error category from
                   search.ledger_search._classify_tactic_error.
        child_id:  id of the resulting state. Set only when outcome == "success".
        error:     The raw Lean error text (empty on success). Kept verbatim
                   (the caller is responsible for capping pathological sizes,
                   e.g. apply?/exact? "Try this" dumps) so the director sees
                   what Lean actually said, not just a category label.
    """
    parent_id: str
    tactic: str
    outcome: str
    child_id: str | None = None
    error: str = ""


@dataclass
class Ledger:
    """
    Full record of a single proof search attempt.

    Attributes:
        frontier:  Open, unexhausted states, keyed by a short stable id
                   (ProofState.stable_hash()[:8]).
        entries:   Every tactic attempted across the whole search — used to
                   summarize dead branches back to the LLM.
        abandoned: Ids the LLM has explicitly given up on. Removed from the
                   frontier at the moment of abandonment, but NOT a
                   permanent blacklist — see add_state.
        reasoning: The director's most recent stated natural-language plan
                   for each state, keyed by state id. Otherwise a director
                   call's reasoning is discarded the moment the turn ends —
                   this is the only memory of "why" that persists across
                   turns for a given branch.
    """
    frontier: dict[str, ProofState] = field(default_factory=dict)
    entries: list[LedgerEntry] = field(default_factory=list)
    abandoned: set[str] = field(default_factory=set)
    reasoning: dict[str, str] = field(default_factory=dict)

    def add_state(self, state: ProofState) -> str:
        """
        Register a state as open, always — even if a state with this exact
        id was abandoned earlier in the search.

        A state's id is a hash of its goals only, not of how it was
        reached, so two independent tactic paths can legitimately converge
        on the identical logical state. Refusing to re-register an id that
        was ever abandoned — regardless of which branch abandoned it or
        why — used to silently drop that state: add_state still returned
        the id as if it had succeeded, but nothing was inserted into
        frontier, so a newly-verified success from an unrelated branch
        could vanish with no record of it as either a success or a
        failure. Confirmed live: a trace showed the same trivially-true
        goal proposed and (per the Lean error log) never once recorded as
        tried, because every successful close of it collided with an
        unrelated earlier abandon and was thrown away before the director
        could ever see the result.
        """
        state_id = state.stable_hash()[:8]
        self.frontier[state_id] = state
        return state_id

    def record_success(self, parent_id: str, tactic: str, child_id: str) -> None:
        self.entries.append(LedgerEntry(parent_id, tactic, "success", child_id))

    def record_failure(self, parent_id: str, tactic: str, category: str, error: str = "") -> None:
        self.entries.append(LedgerEntry(parent_id, tactic, category, None, error))

    def abandon(self, state_ids: list[str]) -> None:
        """Permanently remove states from consideration."""
        for sid in state_ids:
            self.frontier.pop(sid, None)
            self.abandoned.add(sid)

    def failures_for(self, state_id: str) -> list[LedgerEntry]:
        """All failed attempts recorded against a given state, in order."""
        return [
            e for e in self.entries
            if e.parent_id == state_id and e.outcome != "success"
        ]

    def set_reasoning(self, state_id: str, text: str) -> None:
        """Record the director's stated plan for a state. No-op on blank text."""
        if text:
            self.reasoning[state_id] = text
