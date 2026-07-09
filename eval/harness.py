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
    success: bool        # True if any trial succeeded (pass@k)
    passes: int          # number of trials that succeeded
    trials: int          # total trials run
    nodes_visited: int   # avg nodes per trial (rounded)
    elapsed_ms: float    # total elapsed across all trials
    proof_trace: list[str]  # from first successful trial (empty if none)


@dataclass
class EvalSummary:
    timestamp: str
    policy: str
    model: str
    workers: int
    budget: int
    trials: int
    total: int
    passed: int          # problems with at least one passing trial (pass@k)
    pass_rate: float     # passed / total  (pass@k rate)
    mean_pass_rate: float  # mean per-problem pass rate across trials (pass@1 estimate)
    by_difficulty: dict[str, dict]   # {tier: {total, passed, pass_rate, mean_pass_rate}}
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
    trials: int = 1,
) -> EvalSummary:
    """
    Run every problem in *problems* through the prover and collect results.

    Executors must already be started (Mathlib loaded). A fresh
    BestFirstSearch is created for each problem so search state never
    leaks between problems; the underlying executors are reused.

    With trials > 1, each problem is attempted `trials` times independently.
    Results report both pass@k (any trial succeeded) and mean pass rate
    (fraction of trials that succeeded, a pass@1 estimate).
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

        passes = 0
        total_nodes = 0
        total_ms = 0.0
        proof_trace: list[str] = []

        for t in range(trials):
            searches = [
                BestFirstSearch(policy=policy, executor=e, value=value)
                for e in executors
            ]
            result = await prove_parallel(
                problem.statement, searches=searches, budget=budget
            )
            if result.success:
                passes += 1
                if not proof_trace:
                    proof_trace = result.proof_trace
            total_nodes += result.nodes_visited
            total_ms += result.elapsed_ms

            if trials > 1:
                status = "✓" if result.success else "✗"
                print(status, end="", flush=True)

        avg_nodes = round(total_nodes / trials)
        success = passes > 0

        if trials == 1:
            result_single = result  # type: ignore[possibly-undefined]
            status = "✓" if success else "✗"
            suffix = f"  [parse error: {result_single.error}]" if result_single.error else ""
            print(
                f"{status}  {avg_nodes:4d} nodes  {total_ms / 1000:6.1f}s{suffix}"
            )
        else:
            pct = passes / trials
            print(
                f"  {passes}/{trials}  ({pct:4.0%})  "
                f"{avg_nodes:4d} nodes avg  {total_ms / 1000:6.1f}s total"
            )

        results.append(
            ProblemResult(
                name=problem.name,
                difficulty=problem.difficulty,
                tags=list(problem.tags),
                statement=problem.statement,
                success=success,
                passes=passes,
                trials=trials,
                nodes_visited=avg_nodes,
                elapsed_ms=total_ms,
                proof_trace=proof_trace,
            )
        )

    total = len(results)
    passed = sum(r.success for r in results)
    mean_pass_rate = sum(r.passes / r.trials for r in results) / total if total else 0.0

    by_difficulty: dict[str, dict] = {}
    for tier in DIFFICULTIES:
        tier_results = [r for r in results if r.difficulty == tier]
        if tier_results:
            tier_passed = sum(r.success for r in tier_results)
            tier_mean = sum(r.passes / r.trials for r in tier_results) / len(tier_results)
            by_difficulty[tier] = {
                "total": len(tier_results),
                "passed": tier_passed,
                "pass_rate": round(tier_passed / len(tier_results), 3),
                "mean_pass_rate": round(tier_mean, 3),
            }

    return EvalSummary(
        timestamp=timestamp,
        policy=policy_name,
        model=model_name,
        workers=len(executors),
        budget=budget,
        trials=trials,
        total=total,
        passed=passed,
        pass_rate=round(passed / total, 3) if total else 0.0,
        mean_pass_rate=round(mean_pass_rate, 3),
        by_difficulty=by_difficulty,
        results=results,
    )
