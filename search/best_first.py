"""
Best-first search over the proof tree.

Maintains a priority queue of proof states ordered by value estimate.
At each step:
    1. Pop the highest-value state
    2. Ask the policy for k tactic candidates
    3. Verify each candidate in Lean
    4. Push successful results back onto the queue. Remember, these are full proof states, not just tactics — 
       they include the updated goals and hypotheses after applying the tactic.
    5. If any result closes the proof, return success

This is the Phase 2 search algorithm. It handles backtracking naturally
(the priority queue always has the best unexplored state ready) and is
significantly more powerful than greedy search.

The search loop is hardware-agnostic: parallelism is bounded by
executor.capacity, so it automatically scales from MacBook Air (2 workers)
to DGX Spark (10+ workers) with zero code changes.
"""

from __future__ import annotations

import asyncio
import heapq
import time
from dataclasses import dataclass, field
from typing import Optional

from core.executor import LeanExecutor, StepResult
from core.policy import PolicyModel, TacticCandidate
from core.proof_state import ProofState
from core.value import ValueModel


@dataclass
class SearchNode:
    """
    A single node in the proof search tree.

    Attributes:
        state:    The proof state at this node.
        parent:   The parent node. None for the root.
        tactic:   The tactic that produced this node from its parent.
                  Empty string for the root node.
        depth:    Depth in the search tree (same as state.depth).
        value:    Value estimate from the value model, which returns a heuristic score
                  of how promising this node is for finding a proof. Higher is better.
                  Used for priority queue ordering.
    """
    state: ProofState
    parent: Optional[SearchNode]
    tactic: str
    depth: int
    value: float

    # Priority queue comparison — higher value = higher priority.
    # heapq is a min-heap, so we negate value for max-heap behavior.
    def __lt__(self, other: SearchNode) -> bool:
        return self.value > other.value


@dataclass
class ProofResult:
    """
    The result of a proof search attempt.

    Attributes:
        success:      Whether a proof was found.
        proof_trace:  The sequence of tactics that close the proof.
                      Empty if success is False.
        nodes_visited: Total nodes expanded during search.
        elapsed_ms:   Total wall-clock time for the search.
        theorem:      The theorem that was attempted.
    """
    success: bool
    proof_trace: list[str]
    nodes_visited: int
    elapsed_ms: float
    theorem: str

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


class BestFirstSearch:
    """
    Best-first proof search using a priority queue.

    Usage:
        search = BestFirstSearch(policy, executor, value)
        result = await search.prove(theorem, budget=100)

    The search is fully async. Tactic verification calls are parallelized
    up to executor.capacity concurrent Lean workers.
    """

    def __init__(
        self,
        policy: PolicyModel,
        executor: LeanExecutor,
        value: ValueModel,
        k: int = 8,
        premises: list[str] | None = None,
    ):
        """
        Args:
            policy:   Tactic generator (MockPolicy, AnthropicPolicy, etc.)
            executor: Lean verifier (MockExecutor, SubprocessExecutor, etc.)
            value:    State evaluator (HeuristicValue, TrainedValue, etc.)
            k:        Number of tactic candidates to generate per node.
            premises: Mathlib lemma names to pass to the policy as context.
                      In Phase 1 this is empty; Phase 2 uses the retriever.
        """
        self.policy = policy
        self.executor = executor
        self.value = value
        self.k = k
        self.premises = premises or []

    async def prove(
        self,
        theorem: str,
        budget: int = 100,
    ) -> ProofResult:
        """
        Attempt to prove a theorem within a node budget.

        Args:
            theorem: The Lean 4 theorem statement to prove.
            budget:  Maximum number of nodes to expand before giving up.

        Returns:
            ProofResult with success=True and proof_trace if found,
            or success=False if the budget was exhausted.
        """
        start = time.perf_counter()
        nodes_visited = 0

        # Initialize: reset the executor and get the initial proof state
        initial_state = await self.executor.reset(theorem)

        # Handle immediate failure (parse error in theorem statement)
        if initial_state.is_error:
            return ProofResult(
                success=False,
                proof_trace=[],
                nodes_visited=0,
                elapsed_ms=(time.perf_counter() - start) * 1000,
                theorem=theorem,
            )

        # Handle trivially closed theorem (shouldn't happen but be safe)
        if initial_state.is_closed:
            return ProofResult(
                success=True,
                proof_trace=[],
                nodes_visited=0,
                elapsed_ms=(time.perf_counter() - start) * 1000,
                theorem=theorem,
            )

        # Create root node
        root_value = self.value.evaluate(initial_state)
        root = SearchNode(
            state=initial_state,
            parent=None,
            tactic="",
            depth=0,
            value=root_value,
        )

        # Priority queue: (negated_value, tie_breaker, node)
        # tie_breaker ensures stable ordering when values are equal
        counter = 0
        heap: list[tuple[float, int, SearchNode]] = []
        heapq.heappush(heap, (-root.value, counter, root))

        # State cache: avoid re-expanding states we've already seen
        visited: set[str] = set()

        # Semaphore bounds concurrent Lean calls to executor capacity
        sem = asyncio.Semaphore(self.executor.capacity)

        while heap and nodes_visited < budget:
            # Pop the highest-value unexplored node
            _, _, node = heapq.heappop(heap)
            state_hash = node.state.stable_hash()

            # Skip already-visited states (can arrive via different paths)
            if state_hash in visited:
                continue
            visited.add(state_hash)
            nodes_visited += 1

            # Get tactic candidates from the policy
            candidates = await self.policy.get_tactics(
                node.state,
                self.premises,
                k=self.k,
            )

            # Verify all candidates in parallel, bounded by capacity
            results = await self._verify_parallel(node.state, candidates, sem)

            # Process results
            for candidate, result in zip(candidates, results):
                if result.proof_closed:
                    # Found a proof — extract the trace and return
                    trace = self._extract_trace(node, candidate.tactic)
                    return ProofResult(
                        success=True,
                        proof_trace=trace,
                        nodes_visited=nodes_visited,
                        elapsed_ms=(time.perf_counter() - start) * 1000,
                        theorem=theorem,
                    )

                if result.success:
                    # Tactic succeeded but proof not closed — add to queue
                    next_state = result.next_state
                    next_hash = next_state.stable_hash()
                    if next_hash not in visited:
                        next_value = self.value.evaluate(next_state)
                        counter += 1
                        next_node = SearchNode(
                            state=next_state,
                            parent=node,
                            tactic=candidate.tactic,
                            depth=node.depth + 1,
                            value=next_value,
                        )
                        heapq.heappush(heap, (-next_value, counter, next_node))

                # Failed tactics are simply discarded — natural backtracking

        # Budget exhausted or queue empty — search failed
        return ProofResult(
            success=False,
            proof_trace=[],
            nodes_visited=nodes_visited,
            elapsed_ms=(time.perf_counter() - start) * 1000,
            theorem=theorem,
        )

    async def _verify_parallel(
        self,
        state: ProofState,
        candidates: list[TacticCandidate],
        sem: asyncio.Semaphore,
    ) -> list[StepResult]:
        """Verify all tactic candidates concurrently, bounded by semaphore."""

        async def verify_one(candidate: TacticCandidate) -> StepResult:
            async with sem:
                return await self.executor.step(state, candidate.tactic)

        return await asyncio.gather(*[verify_one(c) for c in candidates])

    def _extract_trace(
        self,
        node: SearchNode,
        closing_tactic: str,
    ) -> list[str]:
        """
        Walk parent pointers from node back to root, collecting tactics.
        Append the closing tactic at the end.
        """
        trace = []
        current = node
        while current.parent is not None:
            trace.append(current.tactic)
            current = current.parent
        trace.reverse()
        trace.append(closing_tactic)
        return trace
