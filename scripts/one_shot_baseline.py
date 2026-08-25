#!/usr/bin/env python3
"""
Run the one-shot (no search tree) baseline against real problems and print
the same shape of result LedgerSearch reports, so the two are directly
comparable — this is the actual north-star check: search only earns its
keep if it beats one-shot plus a small, human-scale number of fix attempts.

    python scripts/one_shot_baseline.py --problems imo1968_tetrahedron,tournament_champion
    python scripts/one_shot_baseline.py --problems tournament_champion --max-fixes 2
"""

import argparse
import asyncio
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

from eval.problems import PROBLEM_BY_NAME
from lean.repl import SubprocessExecutor
from policy.anthropic import AnthropicPolicy
from policy.deepseek import DeepSeekPolicy
from search.one_shot import OneShotProve


def parse_args(argv=None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--problems", required=True, metavar="NAMES",
        help="comma-separated problem names from eval/problems.py",
    )
    parser.add_argument("--policy", choices=["anthropic", "deepseek"], default="anthropic")
    parser.add_argument("--model", default=None, metavar="MODEL")
    parser.add_argument("--max-fixes", type=int, default=3, metavar="N")
    parser.add_argument(
        "--no-thinking", action="store_true", default=False,
        help=(
            "disable extended thinking. A weaker, less representative "
            "baseline (real users leave thinking on), but guarantees the "
            "model writes an actual attempt within budget instead of "
            "possibly spending it all on hidden reasoning and never "
            "producing output (seen live on imo1968_tetrahedron up to "
            "60K tokens with thinking on)."
        ),
    )
    return parser.parse_args(argv)


async def _run(args: argparse.Namespace) -> int:
    names = [n.strip() for n in args.problems.split(",") if n.strip()]
    unknown = [n for n in names if n not in PROBLEM_BY_NAME]
    if unknown:
        print(f"error: unknown problem(s): {', '.join(unknown)}", file=sys.stderr)
        return 1

    if args.policy == "deepseek":
        policy = DeepSeekPolicy(model=args.model) if args.model else DeepSeekPolicy()
    else:
        policy = AnthropicPolicy(model=args.model) if args.model else AnthropicPolicy(model="claude-sonnet-5")

    executor = SubprocessExecutor()
    print("Starting Lean worker (loading Mathlib, ~10 min first run)...", end=" ", flush=True)
    await executor.start()
    print("ready.\n")

    prover = OneShotProve(
        policy=policy, executor=executor, max_fixes=args.max_fixes,
        enable_thinking=not args.no_thinking,
    )

    try:
        for name in names:
            problem = PROBLEM_BY_NAME[name]
            print(f"  [{problem.difficulty:7s}] {name:<30s}", end=" ", flush=True)
            outcome = await prover.prove(problem.statement)
            r = outcome.result
            status = "✓" if r.success else "✗"
            suffix = f"  [{r.failure_reason}]" if r.failure_reason else ""
            print(
                f"{status}  {outcome.attempts_used} attempt(s)  "
                f"{r.elapsed_ms / 1000:6.1f}s{suffix}"
            )
            if r.success:
                print(f"              ↳ proof: {' | '.join(r.proof_trace)[:300]}")
            elif r.tactic_errors:
                te_str = ", ".join(
                    f"{k}×{v}" for k, v in sorted(r.tactic_errors.items(), key=lambda x: -x[1])
                )
                print(f"              ↳ errors: {te_str}")
    finally:
        await executor.close()
        await policy.close()

    return 0


def main(argv=None) -> int:
    return asyncio.run(_run(parse_args(argv)))


if __name__ == "__main__":
    sys.exit(main())
