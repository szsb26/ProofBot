#!/usr/bin/env python3
"""
Debug trace: run a real LedgerSearch and record exactly what the director
sees on every turn (the full serialized prompt) and what it returns (the
raw JSON response, parsed decision) — for inspecting the actual information
flow instead of reasoning about it abstractly.

Traces are saved to traces/trace_<name>_<timestamp>.txt, mirroring how
run_eval.py saves to results/eval_<timestamp>.json.

    python scripts/trace_search.py --problem sum_range_formula --budget 8
    python scripts/trace_search.py --problem tournament_champion --budget 20 -k 4
    python scripts/trace_search.py --theorem "theorem foo : n + 0 = n := by" --budget 5
"""

import argparse
import asyncio
import sys
from datetime import datetime
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

from core.trace import TracingPolicy
from eval.problems import PROBLEM_BY_NAME
from lean.repl import SubprocessExecutor
from policy.anthropic import AnthropicPolicy
from policy.deepseek import DeepSeekPolicy
from search.ledger_search import LedgerSearch

TRACES_DIR = Path(__file__).parent.parent / "traces"


def parse_args(argv=None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Trace a LedgerSearch run turn by turn — every prompt "
        "sent to the director and every response received."
    )
    parser.add_argument(
        "--problem", default=None, metavar="NAME",
        help="Problem name from eval/problems.py (see PROBLEM_BY_NAME)",
    )
    parser.add_argument(
        "--theorem", default=None, metavar="STATEMENT",
        help='Raw Lean 4 theorem statement, e.g. "theorem foo : n + 0 = n := by" '
        "(alternative to --problem)",
    )
    parser.add_argument(
        "--policy", choices=["deepseek", "anthropic"], default="deepseek",
    )
    parser.add_argument("--budget", "-b", type=int, default=8, metavar="N")
    parser.add_argument("-k", type=int, default=6, metavar="K")
    parser.add_argument(
        "--output", "-o", default=None, metavar="PATH",
        help="Output file (default: traces/trace_<name>_<timestamp>.txt)",
    )
    return parser.parse_args(argv)


async def _run(args: argparse.Namespace) -> Path:
    if args.problem:
        if args.problem not in PROBLEM_BY_NAME:
            print(f"error: unknown problem {args.problem!r}", file=sys.stderr)
            sys.exit(1)
        theorem = PROBLEM_BY_NAME[args.problem].statement
        name = args.problem
    elif args.theorem:
        theorem = args.theorem
        name = "custom"
    else:
        print("error: provide --problem or --theorem", file=sys.stderr)
        sys.exit(1)

    TRACES_DIR.mkdir(exist_ok=True)
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    output_path = Path(args.output) if args.output else TRACES_DIR / f"trace_{name}_{timestamp}.txt"

    executor = SubprocessExecutor()
    inner_policy = DeepSeekPolicy() if args.policy == "deepseek" else AnthropicPolicy()
    policy = TracingPolicy(inner_policy, verbose=True)
    search = LedgerSearch(policy=policy, executor=executor, k=args.k)

    print("Starting Lean worker (loading Mathlib)...", flush=True)
    await executor.start()
    print("ready.\n", flush=True)

    result = await search.prove(theorem, budget=args.budget)

    footer = (
        f"\n{'=' * 80}\nFINAL RESULT\n{'=' * 80}\n"
        f"success={result.success}\n"
        f"nodes_visited={result.nodes_visited}\n"
        f"failure_reason={result.failure_reason!r}\n"
        f"proof_trace={result.proof_trace}"
    )
    print(footer)

    with open(output_path, "w") as f:
        f.write("Starting Lean worker (loading Mathlib)...\nready.\n")
        f.write(policy.render())
        f.write("\n")
        f.write(footer)

    await policy.close()
    await executor.close()
    return output_path


def main(argv=None) -> int:
    args = parse_args(argv)
    output_path = asyncio.run(_run(args))
    print(f"Trace saved -> {output_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
