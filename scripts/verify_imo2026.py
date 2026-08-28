#!/usr/bin/env python3
"""
Re-verify the IMO 2026 problems in eval/problems.py.

Those entries carry no reference_proof. Unlike the rest of the `imo` tier there
is no Mathlib Archive entry to lift a proof from, and the upstream proofs run
457-4229 lines apiece — inlining them into a Python string literal would bury
8000 lines of Lean somewhere nobody can read or edit. They live in
benchmarks/imo2026/ instead — which is also where eval/imo2026.py derives the
statements from, so the files this script checks are the same files the eval
set is built out of. This script replays the proofs beside them.

Three checks per problem, all of which have to pass:

  1. solution.lean compiles in THIS harness (our Mathlib pin, not the v4.31.0
     it was written against), with zero errors and zero sorries;
  2. every declaration the eval set draws on depends only on the standard
     axioms — no sorryAx smuggled in behind a `macro` or a stray `native_decide`;
  3. solution.lean proves the SAME thing problem.lean specifies: every shared
     definition byte-identical modulo whitespace, every theorem signature
     identical.

(3) earns its place alongside (1). A solution that quietly weakened its own
statement would compile perfectly and prove nothing about the problem we
actually evaluate on. Together the three are what licenses reading a search
failure on these as a fact about the prover rather than about a mis-stated
problem — the tournament_champion lesson, which cost several full-budget runs
against a theorem that was simply false. See scripts/verify_problem_set.py for
the same discipline applied to the reference_proof-carrying problems.

    python scripts/verify_imo2026.py
    python scripts/verify_imo2026.py --problems Q1,Q5
"""

import argparse
import asyncio
import re
import sys
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

from eval.problems import PROBLEMS
from lean.repl import SubprocessExecutor

BENCHMARK_DIR = Path(__file__).parent.parent / "benchmarks" / "imo2026" / "IMO2026"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
DECL_KINDS = ("theorem ", "lemma ", "def ", "noncomputable def ", "abbrev ", "inductive ")


def eval_targets() -> dict[str, list[str]]:
    """
    Map "Q1" -> the declarations the eval set actually draws on, read off the
    `source` field of every imo2026 EvalProblem. Deriving it from the problem
    set rather than hardcoding it means adding an entry there extends the
    verification automatically, and a typo'd source shows up as a missing
    declaration instead of silently going unchecked.
    """
    out: dict[str, list[str]] = defaultdict(list)
    pat = re.compile(r"benchmarks/imo2026/IMO2026/(Q\d)/problem\.lean \((\w+)\)")
    for p in PROBLEMS:
        if "imo2026" not in p.tags:
            continue
        m = pat.fullmatch(p.source)
        if not m:
            raise ValueError(f"{p.name}: unparseable source {p.source!r}")
        out[m.group(1)].append(m.group(2))
    return dict(out)


def declarations(path: Path) -> dict[str, str]:
    """name -> full source text, for every top-level declaration in a Lean file."""
    lines = path.read_text().splitlines()
    out: dict[str, str] = {}
    i = 0
    while i < len(lines):
        kind = next((k for k in DECL_KINDS if lines[i].startswith(k)), None)
        if kind is None:
            i += 1
            continue
        name = lines[i][len(kind):].split()[0].split("(")[0].split(":")[0]
        block = [lines[i]]
        i += 1
        while i < len(lines) and lines[i][:1] in (" ", "\t") and lines[i].strip():
            block.append(lines[i])
            i += 1
        out[name] = "\n".join(block)
    return out


def norm(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def signature(text: str) -> str:
    """Everything up to the proof — what the declaration actually claims."""
    return norm(text.split(":= by")[0] if ":= by" in text else text)


def check_statements_match(q: str, targets: list[str]) -> list[str]:
    """Check (3). Returns a list of problems found; empty means clean."""
    d = BENCHMARK_DIR / q
    problem, solution = declarations(d / "problem.lean"), declarations(d / "solution.lean")
    issues = []
    for name, text in problem.items():
        if name in targets:
            continue
        if name not in solution:
            issues.append(f"definition {name} missing from solution.lean")
        elif norm(text) != norm(solution[name]):
            issues.append(f"definition {name} differs between problem.lean and solution.lean")
    for name in targets:
        if name not in problem:
            issues.append(f"{name} is not declared in problem.lean")
        elif name not in solution:
            issues.append(f"{name} is not declared in solution.lean")
        elif signature(problem[name]) != signature(solution[name]):
            issues.append(f"{name} signature differs — solution.lean proves something else")
    return issues


def namespace_of(path: Path) -> str:
    """Prefix declarations need for #print axioms, e.g. 'TriangleGame.'."""
    for line in path.read_text().splitlines():
        if line.startswith("namespace "):
            return line.split()[1] + "."
    return ""


async def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--problems", default=None, help="comma-separated, e.g. Q1,Q5")
    args = ap.parse_args(argv)

    targets = eval_targets()
    if args.problems:
        wanted = [q.strip() for q in args.problems.split(",") if q.strip()]
        unknown = [q for q in wanted if q not in targets]
        if unknown:
            print(f"unknown problem(s): {', '.join(unknown)}. "
                  f"Known: {', '.join(sorted(targets))}")
            return 2
        targets = {q: targets[q] for q in wanted}

    print(f"{len(targets)} problem(s), "
          f"{sum(len(v) for v in targets.values())} declaration(s) used by the eval set\n")

    # Check (3) needs no Lean, so do it first — a signature mismatch makes the
    # compile meaningless and we may as well not pay for Mathlib to find out.
    failures: list[tuple[str, str]] = []
    for q in sorted(targets):
        for issue in check_statements_match(q, targets[q]):
            failures.append((q, issue))
            print(f"  FAIL  {q}  {issue}", flush=True)
    if failures:
        print(f"\n{len(failures)} statement mismatch(es) — not compiling anything.")
        return 1
    print("  statements match problem.lean in all cases ✓\n")

    ex = SubprocessExecutor()
    print("Starting Lean worker (loading Mathlib)...", end=" ", flush=True)
    await ex.start()
    print("ready.\n", flush=True)
    worker = ex._worker

    try:
        for q in sorted(targets):
            path = BENCHMARK_DIR / q / "solution.lean"
            # `import Mathlib` is already in the REPL's base environment; a
            # second import inside a cmd is an error, not a no-op.
            source = "\n".join(
                l for l in path.read_text().splitlines() if l.strip() != "import Mathlib"
            )
            print(f"  {q} ({len(source.splitlines())} lines)...", end=" ", flush=True)
            try:
                resp = await worker._send(
                    {"cmd": source, "env": worker._base_env}, timeout=7200.0
                )
            except Exception as e:
                failures.append((q, f"raised {type(e).__name__}"))
                print(f"FAIL raised {type(e).__name__}", flush=True)
                continue

            errors = [m for m in resp.get("messages", []) if m.get("severity") == "error"]
            if "message" in resp and "sorries" not in resp and not resp.get("messages"):
                why = f"error: {str(resp['message'])[:90]}"
            elif errors:
                why = f"{len(errors)} error(s), first: {errors[0].get('data','')[:90]}"
            elif resp.get("sorries"):
                why = f"{len(resp['sorries'])} sorry/sorries left open"
            else:
                why = None
            if why:
                failures.append((q, why))
                print(f"FAIL {why}", flush=True)
                continue
            print("compiled", flush=True)

            prefix = namespace_of(path)
            for decl in targets[q]:
                full = prefix + decl
                axresp = await worker._send(
                    {"cmd": f"#print axioms {full}", "env": resp["env"]}, timeout=300.0
                )
                said = " ".join(m.get("data", "") for m in axresp.get("messages", []))
                found = {a.strip() for a in
                         re.sub(r"^.*axioms: \[|\]$", "", said).split(",") if a.strip()}
                if "does not depend on any axioms" in said:
                    found = set()
                if not said or ("axioms:" not in said and not found):
                    failures.append((q, f"{full}: no axiom report ({said[:80]})"))
                    print(f"      FAIL  {full}: no axiom report", flush=True)
                elif found - STANDARD_AXIOMS:
                    failures.append((q, f"{full} depends on {sorted(found - STANDARD_AXIOMS)}"))
                    print(f"      FAIL  {full} depends on "
                          f"{sorted(found - STANDARD_AXIOMS)}", flush=True)
                else:
                    print(f"      ok    {full}", flush=True)
    finally:
        await ex.close()

    print()
    if failures:
        print(f"{len(failures)} FAILED — these problems are not trustworthy:")
        for q, why in failures:
            print(f"   {q}: {why}")
        return 1
    n = sum(len(v) for v in targets.values())
    print(f"all {n} declaration(s) across {len(targets)} problem(s) compile from "
          f"benchmarks/imo2026/ with no sorries and standard axioms only ✓")
    return 0


if __name__ == "__main__":
    sys.exit(asyncio.run(main()))
