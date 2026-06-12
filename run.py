#!/usr/bin/env python3
"""
Command-line interface for the Lean 4 theorem prover.

Mathematicians can use this directly without writing Python:

    python run.py "theorem foo : ∀ n : Nat, n + 0 = n := by"
    python run.py "theorem foo : ..." --workers 4 --budget 50

Set ANTHROPIC_API_KEY in your environment (or .env file) before running.
"""

import argparse
import asyncio
import os
import sys

from dotenv import load_dotenv

from lean.repl import SubprocessExecutor, LEAN_PROJECT_DIR
from lean.mock_executor import MockExecutor
from policy.anthropic import AnthropicPolicy
from policy.mock import MockPolicy
from search.best_first import BestFirstSearch, prove_parallel
from value.heuristic import HeuristicValue


def parse_args(argv=None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog="run.py",
        description="Prove a Lean 4 theorem using LLM-guided best-first search.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
examples:
  # prove a theorem (reads ANTHROPIC_API_KEY from environment)
  python run.py "theorem foo : ∀ n : Nat, n + 0 = n := by"

  # run 4 independent searches in parallel
  python run.py "theorem foo : ∀ n : Nat, n + 0 = n := by" --workers 4

  # expand up to 200 nodes per search before giving up
  python run.py "theorem foo : ..." --budget 200

  # test without an API key or Lean installation (uses fixed tactics)
  python run.py "theorem foo : ∀ n : Nat, n + 0 = n := by" --policy mock
        """,
    )
    parser.add_argument(
        "theorem",
        help='Lean 4 theorem statement (must end with ":= by")',
    )
    parser.add_argument(
        "--workers", "-k",
        type=int,
        default=1,
        metavar="K",
        help="number of parallel proof searches (default: 1)",
    )
    parser.add_argument(
        "--budget", "-b",
        type=int,
        default=100,
        metavar="N",
        help="max nodes expanded per search before giving up (default: 100)",
    )
    parser.add_argument(
        "--policy",
        choices=["anthropic", "mock"],
        default="anthropic",
        help="tactic generation policy: anthropic (default) or mock (no API calls, for testing)",
    )
    parser.add_argument(
        "--tactics",
        default="simp,ring,omega,intro n,aesop,linarith,norm_num,tauto",
        help="comma-separated tactic list for --policy mock",
    )
    parser.add_argument(
        "--model",
        default="claude-haiku-4-5-20251001",
        metavar="MODEL",
        help="Claude model ID (default: claude-haiku-4-5-20251001)",
    )
    parser.add_argument(
        "--api-key",
        default=None,
        metavar="KEY",
        help="Anthropic API key (overrides ANTHROPIC_API_KEY env var)",
    )
    # Hidden flag for testing: forces MockExecutor so no Lean install is needed.
    parser.add_argument(
        "--executor",
        choices=["lean", "mock"],
        default="lean",
        help=argparse.SUPPRESS,
    )
    return parser.parse_args(argv)


def _make_policy(args: argparse.Namespace):
    if args.policy == "mock":
        tactics = [t.strip() for t in args.tactics.split(",") if t.strip()]
        return MockPolicy(tactics=tactics)
    api_key = args.api_key or os.environ.get("ANTHROPIC_API_KEY", "")
    if not api_key:
        print(
            "error: ANTHROPIC_API_KEY is not set.\n"
            "  Set it in your shell:  export ANTHROPIC_API_KEY=sk-...\n"
            "  Or pass it directly:   python run.py ... --api-key sk-...",
            file=sys.stderr,
        )
        sys.exit(1)
    return AnthropicPolicy(model=args.model, api_key=api_key)


def _make_executors(args: argparse.Namespace, k: int):
    if args.executor == "mock":
        return [MockExecutor() for _ in range(k)]
    if not LEAN_PROJECT_DIR.exists():
        print(
            f"error: lean_project not found at {LEAN_PROJECT_DIR}\n"
            "  Build it first:  cd lean_project && lake build",
            file=sys.stderr,
        )
        sys.exit(1)
    return [SubprocessExecutor() for _ in range(k)]


async def _run(args: argparse.Namespace) -> int:
    policy = _make_policy(args)
    executors = _make_executors(args, args.workers)
    value = HeuristicValue()

    _print_header(args)

    use_real_lean = args.executor != "mock"
    if use_real_lean:
        print("Starting Lean workers...", end=" ", flush=True)
        await asyncio.gather(*[e.start() for e in executors])
        print("ready.\n")

    searches = [
        BestFirstSearch(policy=policy, executor=e, value=value)
        for e in executors
    ]

    try:
        result = await prove_parallel(args.theorem, searches=searches, budget=args.budget)
    finally:
        if use_real_lean:
            await asyncio.gather(*[e.close() for e in executors])
        if hasattr(policy, "close"):
            await policy.close()

    _print_result(args, result)
    return 0 if result.success else 1


def _print_header(args: argparse.Namespace) -> None:
    workers_str = f"{args.workers} worker" + ("s" if args.workers > 1 else "")
    policy_str = f"anthropic ({args.model})" if args.policy == "anthropic" else "mock"
    print(f"\nTheorem : {args.theorem.strip()}")
    print(f"Search  : {workers_str}, budget={args.budget}, policy={policy_str}\n")


def _print_result(args: argparse.Namespace, result) -> None:
    if result.success:
        print(f"✓  Proof found in {result.elapsed_ms / 1000:.1f}s ({result.nodes_visited} nodes)\n")
        print("Lean 4 proof:")
        theorem = args.theorem.strip()
        if not theorem.endswith(":= by"):
            theorem = theorem + " := by"
        print(f"  {theorem}")
        for tactic in result.proof_trace:
            print(f"    {tactic}")
        print()
    else:
        print(
            f"✗  No proof found "
            f"({result.nodes_visited} nodes, {result.elapsed_ms / 1000:.1f}s)\n"
            f"   Try increasing --budget or --workers."
        )


def main(argv=None) -> int:
    load_dotenv()
    args = parse_args(argv)
    return asyncio.run(_run(args))


if __name__ == "__main__":
    sys.exit(main())
