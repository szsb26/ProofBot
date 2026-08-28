"""
LLM-guided proof search over a Ledger.

Maintains a Ledger of every open proof state and every tactic attempted
against it. At each step:
    1. Ask the policy to choose which open state to continue from — and
       optionally abandon any state it considers a dead end — plus a single
       tactic for its chosen state (PolicyModel.get_next_action)
    2. Verify the tactic in Lean
    3. Push a successful result back onto the ledger's frontier
    4. If the result closes the proof, return success

There is deliberately no "propose k independent tactic candidates per turn"
mechanism. That design let a single turn spawn several permanent sibling
frontier branches at once, and in practice the model often used the k slots
to encode fragments of one sequential plan rather than genuinely independent
alternatives — producing frontier growth that outpaced one-state-per-turn
triage ("tree poisoning"). A single tactic (optionally ';'-chained, or using
Lean's `first | ... | ...` to hedge within one turn) removes the mechanism
without removing the model's ability to plan multi-step or hedge.

There is no value function and no priority queue. Earlier versions of this
search ranked states with a hand-coded heuristic (goal count + depth) driving
a priority queue; navigation is now entirely the LLM's judgment, informed by
the full ledger rather than one isolated state per call. An eval comparison
across the hard/stretch problem tiers showed this design matches or exceeds
the heuristic-driven version (pass@1 76%→86%, pass@5 80%→100%) while removing
an entire component, so the old design was retired.

The search loop is hardware-agnostic: parallelism is bounded by
executor.capacity, so it automatically scales from MacBook Air (2 workers)
to DGX Spark (10+ workers) with zero code changes.
"""

from __future__ import annotations

import asyncio
import logging
import re
import time
from dataclasses import dataclass

from core.executor import LeanExecutor
from core.ledger import Ledger
from core.policy import PolicyModel

# Reject sorry/admit anywhere in a tactic, not just as the whole tactic —
# both are valid Lean terms, so they can be smuggled in nested inside an
# otherwise legitimate-looking tactic (e.g. "exact absurd hcard (by sorry)").
# Word boundaries avoid false positives on identifiers that merely contain
# these substrings.
_BANNED_TACTIC_PATTERN = re.compile(r"\b(sorry|admit)\b")

logger = logging.getLogger(__name__)


def _contains_banned_tactic(tactic: str) -> bool:
    return bool(_BANNED_TACTIC_PATTERN.search(tactic))


@dataclass
class ProofResult:
    """
    The result of a proof search attempt.

    Attributes:
        success:        Whether a proof was found.
        proof_trace:    The sequence of tactics that close the proof.
        nodes_visited:  Total director calls made during search.
        elapsed_ms:     Total wall-clock time for the search.
        theorem:        The theorem that was attempted.
        error:          Parse/init error; non-empty when nodes_visited == 0.
        failure_reason: Why the search failed (budget_exhausted,
                        frontier_exhausted, parse_error). Empty on success.
    """
    success: bool
    proof_trace: list[str]
    nodes_visited: int
    elapsed_ms: float
    theorem: str
    error: str = ""
    failure_reason: str = ""

    def __repr__(self) -> str:
        if self.success:
            return (
                f"ProofResult(success=True, "
                f"steps={len(self.proof_trace)}, "
                f"nodes={self.nodes_visited}, "
                f"time={self.elapsed_ms:.1f}ms)"
            )
        return (
            f"ProofResult(success=False, "
            f"nodes={self.nodes_visited}, "
            f"time={self.elapsed_ms:.1f}ms)"
        )


class LedgerSearch:
    """
    LLM-guided proof search backed by a Ledger.

    Usage:
        search = LedgerSearch(policy, executor)
        result = await search.prove(theorem, budget=100)

    The search is fully async. Tactic verification calls for a chosen state
    are parallelized up to executor.capacity concurrent Lean workers.
    """

    def __init__(
        self,
        policy: PolicyModel,
        executor: LeanExecutor,
        premises: list[str] | None = None,
    ):
        """
        Args:
            policy:   Tactic/director generator (MockPolicy, AnthropicPolicy,
                      DeepSeekPolicy). Must implement get_next_action().
            executor: Lean verifier (MockExecutor, SubprocessExecutor, etc.)
            premises: Mathlib lemma names to pass to the policy as context.
        """
        self.policy = policy
        self.executor = executor
        self.premises = premises or []

    async def prove(
        self,
        theorem: str,
        budget: int = 100,
        preamble: str = "",
    ) -> ProofResult:
        """
        Attempt to prove a theorem within a director-call budget.

        Args:
            theorem: The Lean 4 theorem statement to prove.
            budget:  Maximum number of director calls before giving up. Each
                     unit is one LLM call (choose a state + propose one
                     tactic) plus one Lean REPL call.

        Returns:
            ProofResult with success=True and proof_trace if found,
            or success=False if the budget was exhausted or the frontier
            emptied out (every open state was abandoned with nothing new
            found to replace it).
        """
        start = time.perf_counter()
        # Lean needs the two parts separately (the preamble becomes its own
        # command so its declarations are in scope for tactics); the director
        # needs them together, since it cannot reason about `Move` without
        # seeing what a Move is.
        initial_state = await self.executor.reset(theorem, preamble)
        shown_theorem = f"{preamble}\n\n{theorem}" if preamble else theorem

        if initial_state.is_error:
            return ProofResult(
                success=False,
                proof_trace=[],
                nodes_visited=0,
                elapsed_ms=(time.perf_counter() - start) * 1000,
                theorem=theorem,
                error=initial_state.error or "Lean parse error",
                failure_reason="parse_error",
            )

        if initial_state.is_closed:
            return ProofResult(
                success=True,
                proof_trace=[],
                nodes_visited=0,
                elapsed_ms=(time.perf_counter() - start) * 1000,
                theorem=theorem,
            )

        calls = 0

        ledger = Ledger()
        ledger.add_state(initial_state)

        while ledger.frontier and calls < budget:
            calls += 1

            resp = await self.policy.get_next_action(shown_theorem, ledger, self.premises)
            # A state named as both chosen and abandoned in the same turn is
            # a self-contradictory response — choosing it is a clear signal
            # to keep it, so drop it from the abandon list rather than
            # abandoning the very state we're about to work on.
            abandoned_ids = [
                sid for sid in resp.abandoned_state_ids if sid != resp.chosen_state_id
            ]
            # Never let an abandonment empty the frontier. The loop below
            # terminates on `not ledger.frontier`, so honouring such a request
            # ends the whole search — and the director is pruning, not asking
            # to stop. Observed live on imo2011_q3: turn 25 abandoned 11
            # states at once and the search reported frontier_exhausted with
            # HALF its 50-call budget unspent. Deciding when to stop is the
            # budget's job, not the model's.
            clearing = [sid for sid in abandoned_ids if sid in ledger.frontier]
            if clearing and len(clearing) >= len(ledger.frontier):
                logger.info(
                    "ignoring abandon of %d state(s): would empty the frontier",
                    len(clearing),
                )
            else:
                ledger.abandon(abandoned_ids, resp.abandon_reason)

            state = ledger.frontier.get(resp.chosen_state_id)
            if state is None:
                # Abandoned on an EARLIER turn and now explicitly chosen
                # again. Re-selection is the clearest signal the abandonment
                # was premature, so honour it rather than discarding the
                # turn — the same reasoning as the same-turn guard above.
                # This was pure waste before: 24 of 50 turns in one
                # imo2005_q3 trial, 20 of 50 in an imo1968_tetrahedron one.
                state = ledger.restore(resp.chosen_state_id)
            if state is None:
                # An id we have genuinely never held — hallucinated or stale.
                # Nothing to expand this turn — try again next call.
                continue

            ledger.set_reasoning(resp.chosen_state_id, resp.reasoning)

            if _contains_banned_tactic(resp.tactic):
                # Nothing legitimate to try this turn — try again next call.
                continue

            result = await self.executor.step(state, resp.tactic)

            # Every genuinely-verified sub-step of a chained tactic (e.g.
            # "intro n; simp; omega") becomes its own frontier state, not
            # just the chain's final outcome — otherwise a multi-step
            # tactic is all-or-nothing: if it succeeds, only the end state
            # is reachable; if a later step fails, everything earlier that
            # DID compile is silently thrown away. This gives the director
            # real checkpoints to continue from instead of only ever
            # re-authoring a whole new multi-step attempt from the last
            # accepted state.
            for checkpoint in result.intermediate_states:
                checkpoint_id = ledger.add_state(checkpoint)
                ledger.set_reasoning(checkpoint_id, resp.reasoning)

            if result.proof_closed:
                return ProofResult(
                    success=True,
                    proof_trace=list(result.next_state.tactic_trace),
                    nodes_visited=calls,
                    elapsed_ms=(time.perf_counter() - start) * 1000,
                    theorem=theorem,
                )

            if result.success:
                new_id = ledger.add_state(result.next_state)
                ledger.set_reasoning(new_id, resp.reasoning)
                # Record the success, not just failures. A state is never
                # evicted from the frontier after being expanded (so the
                # director can backtrack to it), and stable_hash is
                # goals-only, so re-applying a tactic that already worked
                # lands on the identical child id — the frontier doesn't
                # even change size. Without a record, the director sees
                # that state still open with no evidence it ever touched
                # it, and can re-derive the same successful step forever.
                # Observed live: a DeepSeek run burned 10% of its budget
                # re-running one nlinarith that succeeded every time.
                ledger.record_success(resp.chosen_state_id, resp.tactic, new_id)
            else:
                ledger.record_failure(
                    resp.chosen_state_id, resp.tactic, result.next_state.error or ""
                )

        failure_reason = "frontier_exhausted" if not ledger.frontier else "budget_exhausted"
        return ProofResult(
            success=False,
            proof_trace=[],
            nodes_visited=calls,
            elapsed_ms=(time.perf_counter() - start) * 1000,
            theorem=theorem,
            failure_reason=failure_reason,
        )


async def prove_parallel(
    theorem: str,
    searches: list[LedgerSearch],
    budget: int = 100,
    preamble: str = "",
) -> ProofResult:
    """
    Run k independent LedgerSearch instances concurrently.

    Each search must have its own executor (and thus its own Lean worker
    process) and maintains its own ledger. All k searches attempt the same
    theorem independently — whichever finds a proof first wins.

    Args:
        theorem:  The Lean 4 theorem statement to prove.
        searches: Pre-built LedgerSearch instances, each backed by its own
                  SubprocessExecutor. Create with:
                      [LedgerSearch(policy, SubprocessExecutor())
                       for _ in range(k)]
        budget:   Director-call budget per search instance.

    Returns:
        The first successful ProofResult, or — if all searches fail —
        the result with the most director calls made.
    """
    results = await asyncio.gather(
        *[s.prove(theorem, budget, preamble) for s in searches]
    )
    for r in results:
        if r.success:
            return r
    best = max(results, key=lambda r: r.nodes_visited)
    return ProofResult(
        success=False,
        proof_trace=[],
        nodes_visited=best.nodes_visited,
        elapsed_ms=best.elapsed_ms,
        theorem=theorem,
        failure_reason=best.failure_reason,
    )
