#!/usr/bin/env python3
"""
Command-line interface for the Lean 4 theorem prover.

Mathematicians can use this directly without writing Python:

    python run.py "theorem foo : ∀ n : Nat, n + 0 = n := by"
    python run.py "theorem foo : ..." --workers 4 --budget 50
    python run.py --interactive          # warm session; prove many theorems

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
from policy.deepseek import DeepSeekPolicy
from policy.mock import MockPolicy
from search.ledger_search import LedgerSearch, prove_parallel


def parse_args(argv=None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog="run.py",
        description="Prove a Lean 4 theorem using LLM-guided ledger search.",
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
        nargs="?",
        default=None,
        help='Lean 4 theorem statement (must end with ":= by"); omit when using --interactive',
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
        choices=["anthropic", "deepseek", "mock"],
        default="anthropic",
        help="tactic generation policy: anthropic (default), deepseek, or mock (no API calls, for testing)",
    )
    parser.add_argument(
        "--tactics",
        default="simp,ring,omega,intro n,aesop,linarith,norm_num,tauto",
        help="comma-separated tactic list for --policy mock",
    )
    parser.add_argument(
        "--model",
        default=None,
        metavar="MODEL",
        help="model ID to use (default: claude-haiku-4-5-20251001 for anthropic, deepseek-v4-flash for deepseek)",
    )
    parser.add_argument(
        "--api-key",
        default=None,
        metavar="KEY",
        help="API key (overrides ANTHROPIC_API_KEY or DEEPSEEK_API_KEY env var)",
    )
    parser.add_argument(
        "--interactive", "-i",
        action="store_true",
        default=False,
        help="interactive mode: prove multiple theorems in one session without reloading Mathlib",
    )
    # Hidden flag for testing: forces MockExecutor so no Lean install is needed.
    parser.add_argument(
        "--executor",
        choices=["lean", "mock"],
        default="lean",
        help=argparse.SUPPRESS,
    )
    return parser.parse_args(argv)


_POLICY_DEFAULTS = {
    "anthropic": "claude-haiku-4-5-20251001",
    "deepseek": "deepseek-v4-flash",
}

_POLICY_ENV_VARS = {
    "anthropic": "ANTHROPIC_API_KEY",
    "deepseek": "DEEPSEEK_API_KEY",
}


def _make_policy(args: argparse.Namespace):
    if args.policy == "mock":
        tactics = [t.strip() for t in args.tactics.split(",") if t.strip()]
        return MockPolicy(tactics=tactics)

    env_var = _POLICY_ENV_VARS[args.policy]
    api_key = args.api_key or os.environ.get(env_var, "")
    if not api_key:
        print(
            f"error: {env_var} is not set.\n"
            f"  Set it in your shell:  export {env_var}=...\n"
            f"  Or pass it directly:   python run.py ... --api-key ...",
            file=sys.stderr,
        )
        sys.exit(1)

    model = args.model or _POLICY_DEFAULTS[args.policy]
    if args.policy == "anthropic":
        return AnthropicPolicy(model=model, api_key=api_key)
    return DeepSeekPolicy(model=model, api_key=api_key)


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
    load_mathlib = not os.environ.get("LEAN_SKIP_MATHLIB")
    return [SubprocessExecutor(load_mathlib=load_mathlib) for _ in range(k)]


async def _run(args: argparse.Namespace) -> int:
    policy = _make_policy(args)
    executors = _make_executors(args, args.workers)

    _print_header(args)

    use_real_lean = args.executor != "mock"
    if use_real_lean:
        load_mathlib = not os.environ.get("LEAN_SKIP_MATHLIB")
        if load_mathlib:
            print("Starting Lean workers (loading Mathlib, ~5 min first run)...", end=" ", flush=True)
        else:
            print("Starting Lean workers...", end=" ", flush=True)
        await asyncio.gather(*[e.start() for e in executors])
        print("ready.\n")

    searches = [
        LedgerSearch(policy=policy, executor=e)
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
    if args.policy == "mock":
        policy_str = "mock"
    else:
        model = args.model or _POLICY_DEFAULTS.get(args.policy, "")
        policy_str = f"{args.policy} ({model})"
    print(f"\nTheorem : {args.theorem.strip()}")
    print(f"Search  : {workers_str}, budget={args.budget}, policy={policy_str}\n")


def _print_result(args: argparse.Namespace, result) -> None:
    if result.success:
        print(f"✓  Proof found in {result.elapsed_ms / 1000:.1f}s ({result.nodes_visited} nodes)\n")
        print("Lean 4 proof:")
        theorem = result.theorem.strip()
        if not theorem.endswith(":= by"):
            theorem = theorem + " := by"
        print(f"  {theorem}")
        for tactic in result.proof_trace:
            print(f"    {tactic}")
        print()
    elif result.error:
        print(
            f"✗  Parse error ({result.elapsed_ms / 1000:.1f}s)\n"
            f"   {result.error}"
        )
    else:
        print(
            f"✗  No proof found "
            f"({result.nodes_visited} nodes, {result.elapsed_ms / 1000:.1f}s)\n"
            f"   Try increasing --budget or --workers."
        )


async def _interactive(args: argparse.Namespace) -> int:
    """Keep Lean workers warm across multiple theorem submissions."""
    policy = _make_policy(args)
    executors = _make_executors(args, args.workers)

    use_real_lean = args.executor != "mock"
    if use_real_lean:
        load_mathlib = not os.environ.get("LEAN_SKIP_MATHLIB")
        if load_mathlib:
            print("Starting Lean workers (loading Mathlib, ~10 min first run)...", end=" ", flush=True)
        else:
            print("Starting Lean workers...", end=" ", flush=True)
        await asyncio.gather(*[e.start() for e in executors])
        print("ready.")

    workers_str = f"{args.workers} worker" + ("s" if args.workers > 1 else "")
    if args.policy == "mock":
        policy_str = "mock"
    else:
        model = args.model or _POLICY_DEFAULTS.get(args.policy, "")
        policy_str = f"{args.policy} ({model})"
    print(f"\nInteractive mode — {workers_str}, budget={args.budget}, policy={policy_str}")
    print("Enter a theorem statement, or 'quit' to exit.\n")

    try:
        while True:
            try:
                theorem = input("theorem> ").strip()
            except (EOFError, KeyboardInterrupt):
                print("\nGoodbye.")
                break

            if theorem.lower() in ("quit", "exit", "q"):
                print("Goodbye.")
                break

            if not theorem:
                continue

            if not theorem.endswith(":= by"):
                theorem = theorem + " := by"

            searches = [
                LedgerSearch(policy=policy, executor=e)
                for e in executors
            ]

            print("Searching...", flush=True)
            result = await prove_parallel(theorem, searches=searches, budget=args.budget)
            _print_result(args, result)
    finally:
        if use_real_lean:
            await asyncio.gather(*[e.close() for e in executors])
        if hasattr(policy, "close"):
            await policy.close()

    return 0


def main(argv=None) -> int:
    load_dotenv()
    args = parse_args(argv)
    if args.interactive:
        return asyncio.run(_interactive(args))
    if not args.theorem:
        print("error: provide a theorem statement or use --interactive", file=sys.stderr)
        sys.exit(1)
    return asyncio.run(_run(args))


if __name__ == "__main__":
    sys.exit(main())
