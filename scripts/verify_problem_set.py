#!/usr/bin/env python3
"""
Re-verify every problem in eval/problems.py that ships a reference_proof.

Run this after adding problems, and after any Mathlib bump. A problem whose
reference proof no longer closes is either mis-stated or has drifted out of
sync with the library — either way the eval results for it are meaningless
until it is fixed.

This exists because tournament_champion sat in the problem set for weeks as a
provably FALSE theorem. Several full-budget search runs were spent failing to
prove it, and those failures were initially read as model limitations. Nothing
in the repo recorded whether a proof had ever existed, so nothing could catch
it.

    python scripts/verify_problem_set.py
    python scripts/verify_problem_set.py --problems imo
"""

import argparse
import asyncio
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

from eval.problems import PROBLEMS, select_problems
from lean.repl import SubprocessExecutor


async def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--problems", default=None, help="tier or comma-separated names")
    args = ap.parse_args(argv)

    problems = select_problems(args.problems) if args.problems else list(PROBLEMS)
    checkable = [p for p in problems if p.reference_proof]
    skipped = [p for p in problems if not p.reference_proof]

    print(f"{len(checkable)} problem(s) with a reference proof to re-verify")
    if skipped:
        print(f"({len(skipped)} without one — not checkable: "
              f"{', '.join(p.name for p in skipped[:6])}"
              f"{'...' if len(skipped) > 6 else ''})")
    print()

    ex = SubprocessExecutor()
    print("Starting Lean worker (loading Mathlib)...", end=" ", flush=True)
    await ex.start()
    print("ready.\n", flush=True)
    worker = ex._worker

    failures = []
    try:
        for p in checkable:
            stmt = p.statement.rstrip()
            assert stmt.endswith(":= by"), f"{p.name}: statement must end in ':= by'"
            # Helper lemmas the reference proof depends on are not in scope for
            # the statement alone, so they have to be re-declared first. They
            # are never given to the prover — see EvalProblem.reference_preamble.
            pre = (p.reference_preamble + "\n\n") if p.reference_preamble else ""
            cmd = f"{pre}{stmt}\n{p.reference_proof}"
            try:
                resp = await worker._send(
                    {"cmd": cmd, "env": worker._base_env}, timeout=180.0
                )
            except Exception as e:
                failures.append((p.name, f"raised {type(e).__name__}"))
                print(f"  FAIL  {p.name:<20} raised {type(e).__name__}", flush=True)
                continue

            errs = [m for m in resp.get("messages", []) if m.get("severity") == "error"]
            if "message" in resp and "sorries" not in resp:
                why = f"error: {resp['message'][:90]}"
            elif errs:
                why = f"error: {errs[0].get('data','')[:90]}"
            elif resp.get("sorries"):
                why = "proof left sorries"
            else:
                why = None

            if why:
                failures.append((p.name, why))
                print(f"  FAIL  {p.name:<20} {why}", flush=True)
            else:
                print(f"  ok    {p.name}", flush=True)
    finally:
        await ex.close()

    print()
    if failures:
        print(f"{len(failures)} FAILED — these problems are not trustworthy:")
        for n, why in failures:
            print(f"   {n}: {why}")
        return 1
    print(f"all {len(checkable)} reference proofs still close to zero goals ✓")
    return 0


if __name__ == "__main__":
    sys.exit(asyncio.run(main()))
