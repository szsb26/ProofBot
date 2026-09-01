#!/usr/bin/env python3
"""
Per-problem evaluation history, derived from results/*.json.

Answers the questions a pile of timestamped JSON files cannot:
    - has this problem ever been solved, and under which commit?
    - has it regressed since?
    - did its STATEMENT change between runs (which invalidates comparison)?

Derived rather than maintained by hand, because a hand-kept table rots and the
results files are already the source of truth. Nothing here is written back;
run it whenever you want the current picture.

    python scripts/eval_history.py                 # every problem attempted
    python scripts/eval_history.py --tier imo      # one tier
    python scripts/eval_history.py --unsolved      # only never-solved
    python scripts/eval_history.py --runs          # one row per run instead

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
            })

    names = sorted(hist, key=lambda n: (tier_of.get(n, ""), n))
    if args.tier:
        names = [n for n in names if tier_of.get(n) == args.tier]

    print(f"{'problem':<32}{'tier':<9}{'first solved':<14}{'commit':<10}"
          f"{'best':>6}  {'attempts':<10} last")
    shown = 0
    for name in names:
        atts = hist[name]
        wins = [a for a in atts if a["ok"]]
        if args.unsolved and wins:
            continue
        shown += 1
        first = wins[0] if wins else None
        best = min((a["nodes"] for a in wins), default=0)
        passes = sum(a["passes"] for a in atts)
        trials = sum(a["trials"] for a in atts)
        last = atts[-1]
        flag = "*" if (first and first["dirty"]) else ""
        print(f"{name:<32}{tier_of.get(name,'?'):<9}"
              f"{(first['ts'][:8] if first else '—'):<14}"
              f"{((first['commit']+flag) if first else '—'):<10}"
              f"{(best if wins else 0) or '—':>6}  "
              f"{f'{passes}/{trials}':<10} "
              f"{last['ts'][:8]} {'ok' if last['ok'] else 'fail'}")

        if len(statements[name]) > 1:
            print(f"{'':<32}!! STATEMENT CHANGED between runs "
                  f"({len(statements[name])} variants) — results not comparable")

    print(f"\n{shown} problem(s) from {len(runs)} real run(s)")
    print("  * = first solved on a dirty tree; that SHA does not reproduce it")
    return 0


if __name__ == "__main__":
    sys.exit(main())
