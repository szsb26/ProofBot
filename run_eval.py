#!/usr/bin/env python3
"""
Evaluation harness for the Lean 4 theorem prover.

Runs a curated 20-problem set (easy → stretch) and saves pass rate,
node counts, and timing to results/eval_TIMESTAMP.json for longitudinal
comparison across model or algorithm changes.

Lean workers load Mathlib once at startup, then reuse the same warm
executor for every problem — no repeated 10-minute cold starts.

    python run_eval.py                           # all 20 problems, Anthropic default
    python run_eval.py --problems easy           # easy tier only
    python run_eval.py --problems easy,medium    # easy + medium
    python run_eval.py --problems add_zero       # single problem by name
    python run_eval.py --policy deepseek         # switch LLM backend
    python run_eval.py --workers 2 --budget 150  # tune search params
    python run_eval.py --problems hard,stretch --trials 5 --trace  # save traces of failed trials
  python run_eval.py --problems stretch --trials 5 --trace --trace-successes  # save all trials
"""

import argparse
import asyncio
import os
import sys
from pathlib import Path

from dotenv import load_dotenv

from eval.problems import DIFFICULTIES, select_problems
from eval.harness import run_eval
from lean.repl import SubprocessExecutor, LEAN_PROJECT_DIR
from lean.mock_executor import MockExecutor
from policy.anthropic import AnthropicPolicy
from policy.claude_cli import ClaudeCLIPolicy
from policy.deepseek import DeepSeekPolicy
from policy.mock import MockPolicy

RESULTS_DIR = Path(__file__).parent / "results"
TRACES_DIR = Path(__file__).parent / "traces"

_POLICY_DEFAULTS = {
    "anthropic": "claude-haiku-4-5-20251001",
    "claude-cli": "sonnet",
    "deepseek": "deepseek-v4-flash",
}
_POLICY_ENV_VARS = {
    "anthropic": "ANTHROPIC_API_KEY",
    "deepseek": "DEEPSEEK_API_KEY",
}


def parse_args(argv=None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog="eval.py",
        description="Evaluate the theorem prover on a curated problem set.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=f"""
--problems filter syntax:
  difficulty tier   : {', '.join(DIFFICULTIES)}
  problem name      : add_zero, contrapositive, dvd_trans_nat, ... (see eval/problems.py)
  comma-separated   : easy,medium  /  add_zero,binomial_square

examples:
  python run_eval.py
  python run_eval.py --problems easy
  python run_eval.py --problems easy,medium --budget 150
  python run_eval.py --problems add_zero,contrapositive --policy deepseek
  python run_eval.py --workers 2 --budget 200
  python run_eval.py --problems stretch --policy deepseek --trials 5 --trace
        """,
    )
    parser.add_argument(
        "--problems",
        default=None,
        metavar="FILTER",
        help=(
            "comma-separated difficulty tiers or problem names "
            f"(tiers: {', '.join(DIFFICULTIES)}; default: all)"
        ),
    )
    parser.add_argument(
        "--policy",
        choices=["anthropic", "claude-cli", "deepseek", "mock"],
        default="anthropic",
        help=(
            "tactic policy (default: anthropic). \"claude-cli\" shells out to "
            "the claude CLI so usage bills against a Claude subscription "
            "instead of API credits — but the CLI injects ~10K tokens of its "
            "own context per call and supports neither max_tokens nor "
            "temperature, so use a small --budget with it."
        ),
    )
    parser.add_argument(
        "--model",
        default=None,
        metavar="MODEL",
        help="model override (default: claude-haiku-4-5-20251001 or deepseek-v4-flash)",
    )
    parser.add_argument(
        "--api-key",
        default=None,
        metavar="KEY",
        help="API key (overrides ANTHROPIC_API_KEY / DEEPSEEK_API_KEY env var)",
    )
    parser.add_argument(
        "--director-thinking",
        action="store_true",
        default=False,
        help=(
            "enable extended thinking on director calls (no-op for --policy "
            "mock; DeepSeek v4 models reason by default so this can burn "
            "significant tokens before answering)"
        ),
    )
    parser.add_argument(
        "--director-max-tokens",
        type=int,
        default=16000,
        metavar="N",
        help=(
            "max_tokens for director calls (default: 16000). A verbose "
            "response (long reasoning, or thinking) can exhaust this "
            "before its JSON closing brace is ever written, silently "
            "falling back to a blind \"simp\" guess for that turn — raise "
            "this further if that's still happening often."
        ),
    )
    parser.add_argument(
        "--workers", "-k",
        type=int,
        default=1,
        metavar="K",
        help="parallel searches per problem (default: 1)",
    )
    parser.add_argument(
        "--budget", "-b",
        type=int,
        default=100,
        metavar="N",
        help="max nodes expanded per search (default: 100)",
    )
    parser.add_argument(
        "--trials", "-t",
        type=int,
        default=1,
        metavar="K",
        help="independent attempts per problem for pass@k estimation (default: 1)",
    )
    parser.add_argument(
        "--temperature",
        type=float,
        default=1.0,
        metavar="T",
        help="sampling temperature for the LLM policy (default: 0.7)",
    )
    parser.add_argument(
        "--tactics",
        default="simp,ring,omega,intro n,aesop,linarith,norm_num,tauto",
        help="comma-separated tactic list for --policy mock",
    )
    parser.add_argument(
        "--trace",
        action="store_true",
        default=False,
        help=(
            "save a turn-by-turn director prompt/response trace for every "
            "FAILED trial to traces/eval_<timestamp>/ (no-op for --policy mock)"
        ),
    )
    parser.add_argument(
        "--trace-successes",
        action="store_true",
        default=False,
        help=(
            "also save traces for SUCCESSFUL trials (independent of --trace) "
            "— useful for auditing why the model chose a tactic even when it "
            "worked, not just diagnosing failures; off by default since it's "
            "rarely needed (no-op for --policy mock)"
        ),
    )
    # Hidden: lets tests bypass real Lean
    parser.add_argument(
        "--executor",
        choices=["lean", "mock"],
        default="lean",
        help=argparse.SUPPRESS,
    )
    return parser.parse_args(argv)


def _make_policy(args: argparse.Namespace):
    """Return (policy, policy_name, model_name)."""
    if args.policy == "mock":
        tactics = [t.strip() for t in args.tactics.split(",") if t.strip()]
        return MockPolicy(tactics=tactics), "mock", "mock"

    # The CLI authenticates itself (subscription or its own stored
    # credentials), so it needs no API key from us.
    if args.policy == "claude-cli":
        model = args.model or _POLICY_DEFAULTS["claude-cli"]
        return (
            ClaudeCLIPolicy(model=model, director_max_tokens=args.director_max_tokens),
            "claude-cli",
            model,
        )

    env_var = _POLICY_ENV_VARS[args.policy]
    api_key = args.api_key or os.environ.get(env_var, "")
    if not api_key:
        print(
            f"error: {env_var} is not set.\n"
            f"  Set it in your shell:  export {env_var}=...\n"
            f"  Or pass it directly:   python run_eval.py --api-key ...",
            file=sys.stderr,
        )
        sys.exit(1)

    model = args.model or _POLICY_DEFAULTS[args.policy]
    temp = args.temperature
    thinking = args.director_thinking
    director_max_tokens = args.director_max_tokens
    if args.policy == "anthropic":
        return (
            AnthropicPolicy(
                model=model, temperature=temp, api_key=api_key,
                director_thinking=thinking, director_max_tokens=director_max_tokens,
            ),
            "anthropic",
            model,
        )
    return (
        DeepSeekPolicy(
            model=model, temperature=temp, api_key=api_key,
            director_thinking=thinking, director_max_tokens=director_max_tokens,
        ),
        "deepseek",
        model,
    )


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


def _print_summary(summary) -> None:
    multi = summary.trials > 1
    print(f"\n{'─' * 52}")
    if multi:
        print(f"  {summary.trials} trials per problem")
        print(f"  pass@{summary.trials} (any pass)  : {summary.passed}/{summary.total}  ({summary.pass_rate:.0%})")
        print(f"  pass@1  (mean rate) : {summary.mean_pass_rate:.0%}")
    else:
        print(f"  Pass rate : {summary.passed}/{summary.total}  ({summary.pass_rate:.0%})")
    print(f"  By tier   :")
    for tier in DIFFICULTIES:
        if tier in summary.by_difficulty:
            d = summary.by_difficulty[tier]
            bar = "█" * d["passed"] + "░" * (d["total"] - d["passed"])
            if multi:
                print(
                    f"    {tier:8s}  pass@{summary.trials}: {d['passed']}/{d['total']}  "
                    f"({d['pass_rate']:.0%})  mean: {d['mean_pass_rate']:.0%}  {bar}"
                )
            else:
                print(
                    f"    {tier:8s}  {d['passed']}/{d['total']}  "
                    f"({d['pass_rate']:.0%})  {bar}"
                )
    print(f"{'─' * 52}\n")


async def _run(args: argparse.Namespace) -> int:
    try:
        problems = select_problems(args.problems)
    except ValueError as e:
        print(f"error: {e}", file=sys.stderr)
        sys.exit(1)

    policy, policy_name, model_name = _make_policy(args)
    executors = _make_executors(args, args.workers)

    use_real_lean = args.executor != "mock"
    if use_real_lean:
        load_mathlib = not os.environ.get("LEAN_SKIP_MATHLIB")
        if load_mathlib:
            print(
                "Starting Lean workers (loading Mathlib, ~10 min first run)...",
                end=" ",
                flush=True,
            )
        else:
            print("Starting Lean workers...", end=" ", flush=True)
        await asyncio.gather(*[e.start() for e in executors])
        print("ready.\n")

    workers_str = f"{args.workers} worker" + ("s" if args.workers > 1 else "")
    trials_str = f", trials={args.trials}" if args.trials > 1 else ""
    temp_str = f", temp={args.temperature}" if args.executor != "mock" else ""
    thinking_str = ", director_thinking=on" if args.director_thinking else ""
    print(
        f"Evaluating {len(problems)} problem(s) — "
        f"{workers_str}, budget={args.budget}{trials_str}{temp_str}{thinking_str}, "
        f"policy={policy_name} ({model_name})\n"
    )

    try:
        summary = await run_eval(
            problems=problems,
            policy=policy,
            executors=executors,
            budget=args.budget,
            policy_name=policy_name,
            model_name=model_name,
            trials=args.trials,
            trace=args.trace,
            trace_successes=args.trace_successes,
            traces_dir=TRACES_DIR,
        )
    finally:
        if use_real_lean:
            await asyncio.gather(*[e.close() for e in executors])
        if hasattr(policy, "close"):
            await policy.close()

    _print_summary(summary)

    path = summary.save(RESULTS_DIR)
    print(f"Results saved → {path}\n")
    return 0


def main(argv=None) -> int:
    load_dotenv()
    args = parse_args(argv)
    return asyncio.run(_run(args))


if __name__ == "__main__":
    sys.exit(main())
