"""
Core evaluation logic: run a list of EvalProblems against a warm executor
and return a structured EvalSummary with per-problem results and aggregates.
"""

from __future__ import annotations

import json
import os
from dataclasses import asdict, dataclass, field
from datetime import datetime
from pathlib import Path

from eval.problems import DIFFICULTIES, EvalProblem
from search.best_first import BestFirstSearch, prove_parallel
from value.heuristic import HeuristicValue


@dataclass
class ProblemResult:
    name: str
    difficulty: str
    tags: list[str]
    statement: str
    success: bool
    nodes_visited: int
    elapsed_ms: float
    proof_trace: list[str]


@dataclass
class EvalSummary:
    timestamp: str
    policy: str
    model: str
    workers: int
    budget: int
    total: int
    passed: int
    pass_rate: float
    by_difficulty: dict[str, dict]   # {tier: {total, passed, pass_rate}}
    results: list[ProblemResult] = field(default_factory=list)

    def save(self, results_dir: str | Path) -> str:
        """Write to <results_dir>/eval_<timestamp>.json; return the path."""
        os.makedirs(results_dir, exist_ok=True)
        path = os.path.join(results_dir, f"eval_{self.timestamp}.json")
        with open(path, "w") as f:
            json.dump(asdict(self), f, indent=2)
        return path


async def run_eval(
    problems: list[EvalProblem],
    policy,
    executors: list,
    budget: int,
    policy_name: str,
    model_name: str,
) -> EvalSummary:
    """
    Run every problem in *problems* through the prover and collect results.

    Executors must already be started (Mathlib loaded). A fresh
    BestFirstSearch is created for each problem so search state never
    leaks between problems; the underlying executors are reused.
    """
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    value = HeuristicValue()
    results: list[ProblemResult] = []

    for problem in problems:
        print(
            f"  [{problem.difficulty:7s}] {problem.name:<30s}",
            end=" ",
            flush=True,
        )
        searches = [
            BestFirstSearch(policy=policy, executor=e, value=value)
            for e in executors
        ]
        result = await prove_parallel(
            problem.statement, searches=searches, budget=budget
        )
        status = "✓" if result.success else "✗"
        print(
            f"{status}  {result.nodes_visited:4d} nodes  "
            f"{result.elapsed_ms / 1000:6.1f}s"
        )
        results.append(
            ProblemResult(
                name=problem.name,
                difficulty=problem.difficulty,
                tags=list(problem.tags),
                statement=problem.statement,
                success=result.success,
                nodes_visited=result.nodes_visited,
                elapsed_ms=result.elapsed_ms,
                proof_trace=result.proof_trace,
            )
        )

    total = len(results)
    passed = sum(r.success for r in results)

    by_difficulty: dict[str, dict] = {}
    for tier in DIFFICULTIES:
        tier_results = [r for r in results if r.difficulty == tier]
        if tier_results:
            tier_passed = sum(r.success for r in tier_results)
            by_difficulty[tier] = {
                "total": len(tier_results),
                "passed": tier_passed,
                "pass_rate": round(tier_passed / len(tier_results), 3),
            }

    return EvalSummary(
        timestamp=timestamp,
        policy=policy_name,
        model=model_name,
        workers=len(executors),
        budget=budget,
        total=total,
        passed=passed,
        pass_rate=round(passed / total, 3) if total else 0.0,
        by_difficulty=by_difficulty,
        results=results,
    )
