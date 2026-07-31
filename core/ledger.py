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
    """
    parent_id: str
    tactic: str
    outcome: str
    child_id: str | None = None


@dataclass
class Ledger:
    """
    Full record of a single proof search attempt.

    Attributes:
        frontier:  Open, unexhausted states, keyed by a short stable id
                   (ProofState.stable_hash()[:8]).
        entries:   Every tactic attempted across the whole search — used to
                   summarize dead branches back to the LLM.
        abandoned: Ids the LLM has explicitly given up on. Permanently
                   excluded from the frontier and from future prompts.
    """
    frontier: dict[str, ProofState] = field(default_factory=dict)
    entries: list[LedgerEntry] = field(default_factory=list)
    abandoned: set[str] = field(default_factory=set)

    def add_state(self, state: ProofState) -> str:
        """Register a state as open. No-op if it was already abandoned."""
        state_id = state.stable_hash()[:8]
        if state_id not in self.abandoned:
            self.frontier[state_id] = state
        return state_id

    def record_success(self, parent_id: str, tactic: str, child_id: str) -> None:
        self.entries.append(LedgerEntry(parent_id, tactic, "success", child_id))

    def record_failure(self, parent_id: str, tactic: str, category: str) -> None:
        self.entries.append(LedgerEntry(parent_id, tactic, category, None))

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
