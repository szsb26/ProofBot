#!/usr/bin/env python3
"""
Per-problem evaluation history, derived from results/*.json.

Answers the questions a pile of timestamped JSON files cannot:
    - has this problem ever been solved, and under which commit?
    - has it regressed since?
    - did its STATEMENT change between runs (which invalidates comparison)?

Derived rather than maintained by hand, because a hand-kept table rots and the
results files are already the source of truth.

MACHINE-LOCAL BY DESIGN. results/ is gitignored, so this reflects only runs
made on this machine — a collaborator's runs will never appear here, and
yours will not appear in theirs. Do not read a gap as "never attempted
anywhere"; read it as "never attempted here". If a shared record is ever
wanted, that is a decision to commit results/, not something this script can
paper over.

    python scripts/eval_history.py                 # every problem attempted
    python scripts/eval_history.py --tier imo      # one tier
    python scripts/eval_history.py --unsolved      # only never-solved
    python scripts/eval_history.py --runs          # one row per run instead
    python scripts/eval_history.py --write         # also dump to results/eval-history.txt

Runs made by the test suite (policy/model "mock") are excluded by default:
they use LEAN_SKIP_MATHLIB, so simp/ring/omega do not exist and everything
scores 0 — which reads exactly like a catastrophic regression next to a real
run. Pass --include-mock to see them.
"""

import argparse
import json
import glob
import os
import sys
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))
from eval.problems import PROBLEM_BY_NAME  # noqa: E402

# a663c58a (2026-08-01) made proofStatus == "Completed" the only accepted
# success signal. Before it, a tactic that merely emptied the goal list counted
# as a proof — which apply?/exact? do routinely, since they close the current
# state after printing a suggestion. Runs older than this recorded wins that
# were never proofs; see EMPTY-PROOF below for the ones still visible.
PROOFSTATUS_FIX_DATE = "20260801"


def load_runs(include_mock: bool) -> list[dict]:
    runs = []
    for path in sorted(glob.glob("results/eval_*.json")):
        try:
            with open(path) as fh:
                d = json.load(fh)
        except (json.JSONDecodeError, OSError):
            continue
        if not include_mock and (d.get("model") or "") == "mock":
            continue
        d["_path"] = path
        runs.append(d)
    return runs


def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--tier", default=None, help="easy/medium/hard/stretch/imo")
    ap.add_argument("--unsolved", action="store_true", help="only never-solved problems")
    ap.add_argument("--runs", action="store_true", help="list runs instead of problems")
    ap.add_argument("--include-mock", action="store_true")
    ap.add_argument(
        "--write", action="store_true",
        help="also write the table to results/eval-history.txt (gitignored, "
             "like the rest of results/ — this record is machine-local)",
    )
    args = ap.parse_args(argv)

    runs = load_runs(args.include_mock)
    if not runs:
        print("no results found (run from the repo root)")
        return 1

    if args.runs:
        print(f"{'run':<18}{'commit':<10}{'model':<18}{'budget':>7}{'trials':>7}"
              f"{'passed':>8}  problems")
        for r in sorted(runs, key=lambda r: r["timestamp"]):
            commit = (r.get("commit") or "?") + ("*" if r.get("dirty") else "")
            names = ",".join(p["name"] for p in r["results"])[:44]
            print(f"{r['timestamp']:<18}{commit:<10}{str(r.get('model'))[:17]:<18}"
                  f"{r.get('budget',0):>7}{r.get('trials',0):>7}"
                  f"{r.get('passed',0):>3}/{r.get('total',0):<4}  {names}")
        print("\n  * = uncommitted changes present; the SHA does not reproduce this run")
        return 0

    # problem -> chronological attempts
    hist: dict[str, list] = defaultdict(list)
    tier_of: dict[str, str] = {}
    statements: dict[str, set] = defaultdict(set)
    for r in sorted(runs, key=lambda r: r["timestamp"]):
        for p in r["results"]:
            # Benchmark problems only. Test fixtures (trace_test_problem and
            # friends) and problems since removed from the set are not part of
            # the record we are keeping.
            if p["name"] not in PROBLEM_BY_NAME:
                continue
            tier_of[p["name"]] = p.get("difficulty", "?")
            statements[p["name"]].add(" ".join(p.get("statement", "").split()))
            hist[p["name"]].append({
                "ts": r["timestamp"], "commit": r.get("commit") or "?",
                "dirty": r.get("dirty", False), "model": r.get("model") or "?",
                "passes": p.get("passes", 0), "trials": p.get("trials", 1),
                "nodes": p.get("nodes_visited", 0), "ok": p.get("success", False),
                # A "solve" with no tactics is not a proof. Recorded rather
                # than filtered, so the bad rows are visible instead of quietly
                # dropped.
                "empty": bool(p.get("success")) and not p.get("proof_trace"),
                "stale": r["timestamp"][:8] < PROOFSTATUS_FIX_DATE,
            })

    # Every benchmark problem gets a row, attempted or not: a can/cannot-solve
    # table that lists only attempts hides the untested majority.
    TIER_ORDER = {"easy": 0, "medium": 1, "hard": 2, "stretch": 3, "imo": 4}
    for n, prob in PROBLEM_BY_NAME.items():
        tier_of.setdefault(n, prob.difficulty)
    names = sorted(PROBLEM_BY_NAME, key=lambda n: (TIER_ORDER.get(tier_of.get(n, ""), 9), n))
    if args.tier:
        names = [n for n in names if tier_of.get(n) == args.tier]

    print(f"{'problem':<32}{'tier':<9}{'first solved':<14}{'commit':<10}"
          f"{'best':>6}  {'attempts':<10} last")
    shown = 0
    for name in names:
        atts = hist.get(name, [])
        wins = [a for a in atts if a["ok"]]
        if args.unsolved and wins:
            continue
        shown += 1
        if not atts:
            print(f"{name:<32}{tier_of.get(name,'?'):<9}{'—':<14}{'—':<10}"
                  f"{'—':>6}  {'—':<10} never run")
            continue
        first = wins[0] if wins else None
        # Empty-proof records (success with no tactics — see "empty" above)
        # are not proofs, so they must not set the best-node figure. Three such
        # records from 2026-07-03 were rendering solved problems as "best 0".
        real_wins = [a for a in wins if not a["empty"]]
        best = min((a["nodes"] for a in real_wins), default=0)
        passes = sum(a["passes"] for a in atts)
        trials = sum(a["trials"] for a in atts)
        last = atts[-1]
        flag = "*" if (first and first["dirty"]) else ""
        print(f"{name:<32}{tier_of.get(name,'?'):<9}"
              f"{(first['ts'][:8] if first else '—'):<14}"
              f"{((first['commit']+flag) if first else '—'):<10}"
              f"{(str(best) if real_wins else '—'):>6}  "
              f"{f'{passes}/{trials}':<10} "
              f"{last['ts'][:8]} {'ok' if last['ok'] else 'fail'}")

        empties = [a for a in wins if a["empty"]]
        if empties:
            print(f"{'':<32}!! {len(empties)} EMPTY-PROOF 'solve(s)' — success with "
                  f"no tactics, not a proof")
        stale_wins = [a for a in wins if a["stale"]]
        if stale_wins and len(stale_wins) == len(wins):
            print(f"{'':<32}!! all {len(wins)} win(s) predate the proofStatus fix "
                  f"({PROOFSTATUS_FIX_DATE}) — success criterion since rejected")
        if len(statements[name]) > 1:
            print(f"{'':<32}!! STATEMENT CHANGED between runs "
                  f"({len(statements[name])} variants) — results not comparable")

    # Never-attempted problems are part of the picture: a can/cannot-solve
    # table that silently omits them overstates coverage.
    attempted = set(hist)
    never = [n for n, p in PROBLEM_BY_NAME.items() if n not in attempted]
    if args.tier:
        never = [n for n in never if PROBLEM_BY_NAME[n].difficulty == args.tier]

    def trustworthy(n: str) -> bool:
        return any(a["ok"] and not a["empty"] and not a["stale"] for a in hist[n])

    solved = sum(1 for n in names if any(a["ok"] for a in hist[n]))
    trusted = sum(1 for n in names if trustworthy(n))
    print(f"\n{shown} shown | {len(attempted)} attempted | {solved} with a recorded win, "
          f"of which {trusted} under the current success criterion")
    print(f"  {len(never)} NEVER ATTEMPTED of {len(PROBLEM_BY_NAME)} in problems.py")
    print("  * = first solved on a dirty tree; that SHA does not reproduce it")
    print("  (machine-local: results/ is gitignored, so other machines' runs are absent)")
    return 0


def cli(argv=None) -> int:
    """Run main(), echoing to stdout and optionally saving a copy.

    The copy lands in results/, which is gitignored — this record is
    machine-local by design (see the module docstring).
    """
    import contextlib, io
    argv = list(sys.argv[1:] if argv is None else argv)
    want_write = "--write" in argv
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        code = main(argv)
    text = buf.getvalue()
    sys.stdout.write(text)
    if want_write and code == 0:
        dest = Path(__file__).parent.parent / "results" / "eval-history.txt"
        dest.parent.mkdir(exist_ok=True)
        dest.write_text(text)
        print(f"\nwritten to {dest.relative_to(Path(__file__).parent.parent)}")
    return code


if __name__ == "__main__":
    sys.exit(cli())
