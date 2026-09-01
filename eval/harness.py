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

from core.trace import TracingPolicy
from eval.problems import DIFFICULTIES, EvalProblem
from search.ledger_search import LedgerSearch, prove_parallel


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
    failure_modes: dict = field(default_factory=dict)   # search-level: {reason: count}
    failed_trial_traces: list[str] = field(default_factory=list)  # paths, only when --trace is on
    successful_trial_traces: list[str] = field(default_factory=list)  # paths, only when --trace-successes is on


def _provenance() -> dict:
    """Identify the code that produced a run.

    Without this a stored result is uninterpretable: eval_20260827_161523.json
    records 0/3 on IMO 2026 and looks like a capability measurement, but it
    predates 43740dd4 — those problems were unprovable by construction at the
    time. A timestamp alone cannot distinguish the two.

    `dirty` matters as much as the commit: a run made with uncommitted changes
    is not reproducible from the SHA, and during active development that is
    the common case rather than the exception.
    """
    import subprocess

    def _git(*args: str) -> str:
        try:
            return subprocess.run(
                ["git", *args], cwd=Path(__file__).parent.parent,
                capture_output=True, text=True, timeout=5,
            ).stdout.strip()
        except Exception:
            return ""

    toolchain = Path(__file__).parent.parent / "lean_project" / "lean-toolchain"
    return {
        "commit": _git("rev-parse", "--short", "HEAD"),
        "dirty": bool(_git("status", "--porcelain", "--untracked-files=no")),
        "lean_toolchain": toolchain.read_text().strip() if toolchain.exists() else "",
    }


@dataclass
class EvalSummary:
    timestamp: str
    policy: str
    model: str
    workers: int
    budget: int
    trials: int
    # Which code produced this — see _provenance().
    commit: str
    dirty: bool
    lean_toolchain: str
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


def _build_summary(
    results: list[ProblemResult], *, timestamp: str, policy_name: str,
    model_name: str, workers: int, budget: int, trials: int,
) -> EvalSummary:
    """Aggregate whatever results exist so far into an EvalSummary.

    Split out of run_eval so a partial summary can be written after each
    problem — see the incremental save there.
    """
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
        workers=workers,
        budget=budget,
        trials=trials,
        **_provenance(),
        total=total,
        passed=passed,
        pass_rate=round(passed / total, 3) if total else 0.0,
        mean_pass_rate=round(mean_pass_rate, 3),
        by_difficulty=by_difficulty,
        results=results,
    )


async def run_eval(
    problems: list[EvalProblem],
    policy,
    executors: list,
    budget: int,
    policy_name: str,
    model_name: str,
    trials: int = 1,
    trace: bool = False,
    trace_successes: bool = False,
    traces_dir: str | Path = "traces",
    results_dir: str | Path | None = None,
) -> EvalSummary:
    """
    Run every problem in *problems* through the prover and collect results.

    Executors must already be started (Mathlib loaded). A fresh LedgerSearch
    instance is created for each trial so search state never leaks between
    problems; the underlying executors are reused.

    With trials > 1, each problem is attempted `trials` times independently.
    Results report both pass@k (any trial succeeded) and mean pass rate
    (fraction of trials that succeeded, a pass@1 estimate).

    trace: if True, every trial's director calls are captured verbatim (see
    core.trace.TracingPolicy) and — for trials that fail — saved to
    <traces_dir>/eval_<timestamp>/<problem>_trial<N>_worker<M>_failed.txt,
    so a specific failed attempt can be inspected after the fact rather
    than needing to separately reproduce it (which, at temperature=1.0,
    won't give you the same attempt anyway).

    trace_successes: if True, successful trials are ALSO saved (as
    ..._success.txt), for analysis that needs the model's turn-by-turn
    reasoning even when it succeeded — e.g. understanding why it chose a
    particular tactic — which the results JSON's flat proof_trace can't
    show. Off by default since it's rarely needed and adds disk/latency
    overhead; the winning proof_trace is already in the results JSON for
    the common case.

    Both require *policy* to be a BaseLLMPolicy-compatible object (has
    _call_api); if not (e.g. MockPolicy), tracing is silently skipped since
    there's no real LLM call to capture.
    """
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    results: list[ProblemResult] = []

    can_trace = (trace or trace_successes) and hasattr(policy, "_call_api")
    if (trace or trace_successes) and not can_trace:
        print(
            "  (--trace/--trace-successes ignored: policy has no _call_api, "
            "nothing to capture)\n"
        )
    trial_traces_dir = Path(traces_dir) / f"eval_{timestamp}"

    # Raw Lean logging is deliberately gated on --trace/--trace-successes but
    # NOT on can_trace: it hooks the REPL, not the policy, so it works for
    # every policy including mock, and captures the whole run rather than only
    # the trials that happen to fail. One file per executor, since each owns
    # its own REPL subprocess and they run concurrently.
    loggable = [
        (i, ex) for i, ex in enumerate(executors, start=1)
        if hasattr(ex, "set_raw_log_path")
    ]
    if (trace or trace_successes) and loggable:
        lean_log_dir = trial_traces_dir / "lean"
        lean_log_dir.mkdir(parents=True, exist_ok=True)
        for i, ex in loggable:
            ex.set_raw_log_path(lean_log_dir / f"worker{i}.jsonl")

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
        failure_modes: dict[str, int] = {}
        failed_trace_paths: list[str] = []
        success_trace_paths: list[str] = []

        for t in range(trials):
            if can_trace:
                traced_policies = [TracingPolicy(policy) for _ in executors]
                searches = [
                    LedgerSearch(policy=tp, executor=e)
                    for tp, e in zip(traced_policies, executors)
                ]
            else:
                traced_policies = []
                searches = [
                    LedgerSearch(policy=policy, executor=e)
                    for e in executors
                ]
            result = await prove_parallel(
                problem.statement, searches=searches, budget=budget,
                preamble=problem.statement_preamble
            )
            trace_sources = traced_policies

            if result.success:
                passes += 1
                if not proof_trace:
                    proof_trace = result.proof_trace

                if can_trace and trace_successes:
                    trial_traces_dir.mkdir(parents=True, exist_ok=True)
                    for w, tp in enumerate(trace_sources, start=1):
                        path = trial_traces_dir / f"{problem.name}_trial{t + 1}_worker{w}_success.txt"
                        path.write_text(tp.render())
                        success_trace_paths.append(str(path))
            else:
                reason = result.failure_reason or "unknown"
                failure_modes[reason] = failure_modes.get(reason, 0) + 1

                if can_trace and trace:
                    trial_traces_dir.mkdir(parents=True, exist_ok=True)
                    for w, tp in enumerate(trace_sources, start=1):
                        path = trial_traces_dir / f"{problem.name}_trial{t + 1}_worker{w}_failed.txt"
                        path.write_text(tp.render())
                        failed_trace_paths.append(str(path))

            total_nodes += result.nodes_visited
            total_ms += result.elapsed_ms

            if trials > 1:
                status = "✓" if result.success else "✗"
                print(status, end="", flush=True)

        avg_nodes = round(total_nodes / trials)
        success = passes > 0

        failures = trials - passes
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
        if failures > 0 and failure_modes:
            # Search-level reasons only (budget_exhausted / frontier_exhausted /
            # parse_error). Tactic-level error CATEGORIES used to be summarised
            # here too; they were removed because the categoriser was measurably
            # unreliable and nothing consumed the numbers. Run with --trace for
            # the raw Lean errors, which are the ground truth.
            fm_str = ", ".join(
                f"{k}×{v}" for k, v in sorted(failure_modes.items(), key=lambda x: -x[1])
            )
            print(f"              ↳ search: {fm_str}")
        if failed_trace_paths or success_trace_paths:
            print(f"              ↳ traces: {trial_traces_dir}/")

        results.append(
            ProblemResult(
                name=problem.name,
                difficulty=problem.difficulty,
                tags=list(problem.tags),
                # Full text (preamble + theorem) so the record says what was
                # actually proven and stays comparable across refactors that
                # move parts between fields.
                statement=problem.full_statement,
                success=success,
                passes=passes,
                trials=trials,
                nodes_visited=avg_nodes,
                elapsed_ms=total_ms,
                proof_trace=proof_trace,
                failure_modes=failure_modes,
                failed_trial_traces=failed_trace_paths,
                successful_trial_traces=success_trace_paths,
            )
        )

        # Save after every problem, not just at the end. A long run can be
        # cut short by something outside the harness — an exhausted credit
        # balance, a killed process — and without this the whole run's
        # results are lost even though the work was already paid for. Traces
        # are already written per trial; this brings the summary in line.
        if results_dir is not None:
            partial = _build_summary(
                results, timestamp=timestamp, policy_name=policy_name,
                model_name=model_name, workers=len(executors), budget=budget,
                trials=trials,
            )
            partial.save(results_dir)

    return _build_summary(
        results, timestamp=timestamp, policy_name=policy_name,
        model_name=model_name, workers=len(executors), budget=budget,
        trials=trials,
    )
