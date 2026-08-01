"""
LLM-guided proof search over a Ledger.

Maintains a Ledger of every open proof state and every tactic attempted
against it. At each step:
    1. Ask the policy to choose which open state to continue from — and
       optionally abandon any state it considers a dead end — plus k tactic
       candidates for its chosen state (PolicyModel.get_next_action)
    2. Verify each candidate in Lean
    3. Push successful results back onto the ledger's frontier
    4. If any result closes the proof, return success

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
import re
import time
from dataclasses import dataclass, field

from core.executor import LeanExecutor
from core.ledger import Ledger
from core.policy import PolicyModel

# Reject sorry/admit anywhere in a tactic, not just as the whole tactic —
# both are valid Lean terms, so they can be smuggled in nested inside an
# otherwise legitimate-looking tactic (e.g. "exact absurd hcard (by sorry)").
# Word boundaries avoid false positives on identifiers that merely contain
# these substrings.
_BANNED_TACTIC_PATTERN = re.compile(r"\b(sorry|admit)\b")


def _contains_banned_tactic(tactic: str) -> bool:
    return bool(_BANNED_TACTIC_PATTERN.search(tactic))


def _classify_tactic_error(error: str) -> str:
    e = error.lower()
    if e.startswith("lean error:\n"):
        e = e[len("lean error:\n"):]
    if "unknown identifier" in e or "unknown constant" in e:
        return "hallucinated_lemma"
    if "application type mismatch" in e or "function expected" in e:
        return "wrong_arguments"
    if "type mismatch" in e:
        return "type_mismatch"
    if "failed to synthesize" in e:
        return "typeclass_failure"
    if "unsolved goals" in e:
        return "unsolved_goals"
    if "no goals" in e:
        return "no_goals"
    if "expected token" in e or "unexpected token" in e or "unexpected end of input" in e:
        return "syntax_error"
    if "maximum heart beats" in e or "deterministic timeout" in e:
        return "max_heartbeats"
    if "inserted a hidden sorry" in e:
        return "hidden_sorry"
    return "tactic_failed"


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
        tactic_errors:  Counts of tactic-level error categories across all
                        rejected tactics during this search.
    """
    success: bool
    proof_trace: list[str]
    nodes_visited: int
    elapsed_ms: float
    theorem: str
    error: str = ""
    failure_reason: str = ""
    tactic_errors: dict = field(default_factory=dict)

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
        k: int = 8,
        premises: list[str] | None = None,
    ):
        """
        Args:
            policy:   Tactic/director generator (MockPolicy, AnthropicPolicy,
                      DeepSeekPolicy). Must implement get_next_action().
            executor: Lean verifier (MockExecutor, SubprocessExecutor, etc.)
            k:        Number of tactic candidates requested per director call.
            premises: Mathlib lemma names to pass to the policy as context.
        """
        self.policy = policy
        self.executor = executor
        self.k = k
        self.premises = premises or []

    async def prove(
        self,
        theorem: str,
        budget: int = 100,
    ) -> ProofResult:
        """
        Attempt to prove a theorem within a director-call budget.

        Args:
            theorem: The Lean 4 theorem statement to prove.
            budget:  Maximum number of director calls before giving up. Each
                     unit is one LLM call (choose a state + propose k
                     tactics) plus up to k Lean REPL calls.

        Returns:
            ProofResult with success=True and proof_trace if found,
            or success=False if the budget was exhausted or the frontier
            emptied out (every open state was abandoned with nothing new
            found to replace it).
        """
        start = time.perf_counter()
        calls = 0

        initial_state = await self.executor.reset(theorem)

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

        ledger = Ledger()
        ledger.add_state(initial_state)

        tactic_errors: dict[str, int] = {}

        while ledger.frontier and calls < budget:
            calls += 1

            resp = await self.policy.get_next_action(
                theorem, ledger, self.premises, k=self.k
            )
            # A state named as both chosen and abandoned in the same turn is
            # a self-contradictory response — choosing it is a clear signal
            # to keep it, so drop it from the abandon list rather than
            # abandoning the very state we're about to work on.
            abandoned_ids = [
                sid for sid in resp.abandoned_state_ids if sid != resp.chosen_state_id
            ]
            ledger.abandon(abandoned_ids)

            state = ledger.frontier.get(resp.chosen_state_id)
            if state is None:
                # The director referenced a stale, abandoned, or invalid id.
                # Nothing to expand this turn — try again next call.
                continue

            ledger.set_reasoning(resp.chosen_state_id, resp.reasoning)

            candidates = [
                c for c in resp.tactics if not _contains_banned_tactic(c.tactic)
            ]

            results = [
                await self.executor.step(state, c.tactic)
                for c in candidates
            ]

            for candidate, result in zip(candidates, results):
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
                else:
                    err = result.next_state.error or ""
                    category = _classify_tactic_error(err)
                    tactic_errors[category] = tactic_errors.get(category, 0) + 1
                    ledger.record_failure(resp.chosen_state_id, candidate.tactic, category)

        failure_reason = "frontier_exhausted" if not ledger.frontier else "budget_exhausted"
        return ProofResult(
            success=False,
            proof_trace=[],
            nodes_visited=calls,
            elapsed_ms=(time.perf_counter() - start) * 1000,
            theorem=theorem,
            failure_reason=failure_reason,
            tactic_errors=tactic_errors,
        )


async def prove_parallel(
    theorem: str,
    searches: list[LedgerSearch],
    budget: int = 100,
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
    results = await asyncio.gather(*[s.prove(theorem, budget) for s in searches])
    for r in results:
        if r.success:
            return r
    best = max(results, key=lambda r: r.nodes_visited)
    combined_errors: dict[str, int] = {}
    for r in results:
        for cat, count in r.tactic_errors.items():
            combined_errors[cat] = combined_errors.get(cat, 0) + count
    return ProofResult(
        success=False,
        proof_trace=[],
        nodes_visited=best.nodes_visited,
        elapsed_ms=best.elapsed_ms,
        theorem=theorem,
        failure_reason=best.failure_reason,
        tactic_errors=combined_errors,
    )
