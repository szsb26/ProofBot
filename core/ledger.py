"""
Ledger-based proof search state.

A Ledger is a plain record of every attempted tactic and its outcome — it
carries no scores or rankings. Deciding which state to expand next (and when
to give up on a branch) is done by the LLM itself, using the ledger as its
input, rather than by a hand-coded heuristic driving a priority queue.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from core.executor import SentMessage
from core.proof_state import ProofState


@dataclass
class LedgerEntry:
    """
    One attempted tactic and what Lean said about it.

    Attributes:
        parent_id: id of the state the tactic was tried against.
        tactic:    The tactic string sent to Lean.
        outcome:   "success" or "failed". Deliberately just those two — this
                   used to hold an error CATEGORY, but categorising Lean
                   errors by hand-written substring proved unreliable enough
                   to be worse than useless: audited over 2847 real errors
                   from our own traces, two of the nine categories matched
                   strings Lean never emits (so they never once fired) and
                   the catch-all held a third of everything, filing genuine
                   refutations alongside resource failures. Nothing consumed
                   the value, so it is no longer computed. `error` below is
                   the ground truth, and traces (--trace) keep it verbatim.
        child_id:  id of the resulting state. Set only when outcome == "success".
        error:     The raw Lean error text (empty on success). Kept verbatim
                   (the caller is responsible for capping pathological sizes,
                   e.g. apply?/exact? "Try this" dumps) so the director sees
                   what Lean actually said, uncompressed.
        sent:      The messages actually handed to the Lean REPL for this
                   tactic, in order, with how each came back. `tactic` is
                   what the director WROTE; this is what Lean was ASKED.
                   They differ whenever a ';'-chain is split into several
                   messages, and the director cannot otherwise tell — which
                   is how imo2026_q5 spent ~30 turns attributing a harness
                   behaviour to Lean's parser. Empty for entries recorded
                   without reaching Lean (e.g. a banned tactic).
    """
    parent_id: str
    tactic: str
    outcome: str
    child_id: str | None = None
    error: str = ""
    sent: tuple[SentMessage, ...] = ()


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
                   permanent blacklist — see add_state and restore.
        abandon_reasons: The director's stated reason per abandoned state,
                   used to label it in the resumable-abandoned list.
        retired:   States removed by abandon(), kept so a later turn can
                   restore() them. Without this the ProofState was simply
                   dropped, and a director that abandoned a branch and then
                   asked for it back — which happens constantly — got a
                   silently wasted turn (measured: 24 of 50 turns in one
                   imo2005_q3 trial, 20 of 50 in an imo1968_tetrahedron one).
        reasoning: Every stated natural-language plan for each state, keyed
                   by state id, oldest first, each tagged with the turn that
                   wrote it. The director call is stateless — one user
                   message, no conversation history — so this is the ONLY
                   channel by which one turn tells a later turn anything it
                   cannot read off the goal text.

                   It used to hold one plan per state and overwrite. Measured
                   on imo2026_q5: turn 28 worked out that substituting
                   y = f x into hqm yields the tautology 2(f x - x)^2 >= 0,
                   turn 29 chose the same state and overwrote that finding,
                   and turn 37 — with the note gone — proposed the refuted
                   substitution again calling it "NOT just the trivial
                   identity", spending the rest of the budget. 50 turns over
                   31 distinct states means at least 19 plans were destroyed
                   that way.

                   Kept oldest-first and NEVER capped by recency: a
                   "keep the last N" rule reproduces exactly the bug above,
                   dropping turn 28 and keeping turn 29. Negative results
                   accumulate early and stay true.
    """
    frontier: dict[str, ProofState] = field(default_factory=dict)
    entries: list[LedgerEntry] = field(default_factory=list)
    abandoned: set[str] = field(default_factory=set)
    reasoning: dict[str, list[tuple[int, str]]] = field(default_factory=dict)
    retired: dict[str, ProofState] = field(default_factory=dict)
    abandon_reasons: dict[str, str] = field(default_factory=dict)

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
        # If this id was previously abandoned, re-deriving it supersedes the
        # retired copy — otherwise a later abandon()/restore() cycle could
        # resurrect the stale one alongside the live entry.
        self.retired.pop(state_id, None)
        self.abandoned.discard(state_id)
        self.abandon_reasons.pop(state_id, None)
        return state_id

    def record_success(
        self,
        parent_id: str,
        tactic: str,
        child_id: str,
        sent: tuple[SentMessage, ...] = (),
    ) -> None:
        self.entries.append(
            LedgerEntry(parent_id, tactic, "success", child_id, sent=sent)
        )

    def record_failure(
        self,
        parent_id: str,
        tactic: str,
        error: str = "",
        sent: tuple[SentMessage, ...] = (),
    ) -> None:
        self.entries.append(
            LedgerEntry(parent_id, tactic, "failed", None, error, sent=sent)
        )

    def abandon(self, state_ids: list[str], reason: str = "") -> None:
        """
        Remove states from the frontier, retaining them for restore().

        Not permanent: the director prunes speculatively and frequently asks
        for a pruned branch back a turn or two later. Keeping the ProofState
        is what makes honouring that request possible.

        *reason* is the director's own stated `abandon_reason`. It labels the
        state in the resumable-abandoned list so a later turn can tell why
        this branch was parked without having to re-derive it.
        """
        for sid in state_ids:
            state = self.frontier.pop(sid, None)
            if state is not None:
                self.retired[sid] = state
            self.abandoned.add(sid)
            if reason:
                self.abandon_reasons[sid] = reason

    def restore(self, state_id: str) -> ProofState | None:
        """
        Put a previously abandoned state back on the frontier.

        Returns the state, or None if we never had it (an id the director
        hallucinated, or one from a search that never held it).

        Called when the director explicitly selects a state it abandoned on
        an earlier turn. That re-selection is the clearest possible signal
        that the abandonment was premature — the same reasoning behind
        refusing to abandon a state that is being chosen in the same turn.
        Before this existed the turn was silently discarded.
        """
        state = self.retired.pop(state_id, None)
        if state is None:
            return None
        self.frontier[state_id] = state
        self.abandoned.discard(state_id)
        self.abandon_reasons.pop(state_id, None)
        return state

    def failures_for(self, state_id: str) -> list[LedgerEntry]:
        """All failed attempts recorded against a given state, in order."""
        return [
            e for e in self.entries
            if e.parent_id == state_id and e.outcome != "success"
        ]

    def set_reasoning(self, state_id: str, text: str, turn: int) -> None:
        """
        Append the director's stated plan for a state. No-op on blank text.

        Appends rather than overwrites — see the `reasoning` field docs for
        the measured failure that motivated it. An exact repeat of the most
        recent plan is dropped, so a director that re-states the same
        intention verbatim does not pad the prompt.
        """
        if not text:
            return
        history = self.reasoning.setdefault(state_id, [])
        if history and history[-1][1] == text:
            return
        history.append((turn, text))

    def latest_reasoning(self, state_id: str) -> str:
        """The most recent stated plan for a state, or "" if there is none."""
        history = self.reasoning.get(state_id)
        return history[-1][1] if history else ""
