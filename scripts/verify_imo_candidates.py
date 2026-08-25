#!/usr/bin/env python3
"""
Extract IMO problems from Mathlib's Archive and verify each one in OUR harness
before it is allowed into the eval set.

Mathlib proving a theorem in its own CI is not the same as the statement being
correct *here*: our REPL elaborates against `import Mathlib` with no Archive
context, and a statement that silently fails to elaborate — or that we
transcribe wrongly — would land in the problem set unnoticed. That is exactly
how `tournament_champion` sat in the eval set for weeks as a provably FALSE
theorem, with several full-budget search runs spent on it before anyone
checked (see eval/problems.py).

So for each candidate this does two things:

  1. VERIFY THE STATEMENT IS TRUE — replay Mathlib's own proof, including any
     helper lemmas defined alongside it in the Archive file, and require it to
     close to zero goals. If the proof does not land, the candidate is
     rejected rather than guessed at.

  2. VERIFY THE BENCHMARK FORM ELABORATES — the standalone statement (helpers
     stripped, `open` context preserved via `open X in`) must reset cleanly to
     an open goal, since that is the exact string the prover will be handed.

Only candidates passing both are emitted.

Helper lemmas are used ONLY in step 1, never handed to the prover. Finding the
decomposition is the capability under test — the bare `have` mechanic exists so
the model can invent its own sub-lemmas — so leaking Mathlib's would measure the
wrong thing. Imo1959Q1 makes this concrete: its `calculation` helper *is* the
proof, and the headline theorem is a two-line wrapper around it. It also keeps
new problems comparable with the existing ones (imo1968_tetrahedron,
tournament_champion are bare statements) and matches the miniF2F/PutnamBench
convention.

The tradeoff is that a full IMO problem stripped of helpers can be far harder
than the original, so expect low pass rates. That is acceptable while the
failures stay *informative*; if a batch fails identically at turn 1-3, the fix
is to curate easier problems, not to start leaking helpers.

    python scripts/verify_imo_candidates.py --limit 8
    python scripts/verify_imo_candidates.py --only Imo1959Q1,Imo1963Q5
"""

import argparse
import asyncio
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

from lean.repl import LeanWorker, SubprocessExecutor

ARCHIVE = (
    Path(__file__).parent.parent
    / "lean_project/.lake/packages/mathlib/Archive/Imo"
)


def parse_file(path: Path) -> dict | None:
    """Pull the headline theorem, its proof, the file's `open` context, and
    everything else the proof might lean on, out of an Archive file."""
    src = path.read_text()
    body = "\n".join(
        l for l in src.splitlines() if not l.startswith("import ")
    )
    # Drop the module docstring, which can contain characters that confuse
    # a single-line REPL command.
    body = re.sub(r"/-!.*?-/", "", body, flags=re.S)

    opens = re.findall(r"^open\s+([^\n]+?)\s*$", body, re.M)
    # Namespaces declared inside this Archive file (e.g. `namespace Imo1959Q1`)
    # do not exist for a standalone statement, so an `open` naming one would
    # make the benchmark form fail to elaborate. Statements never depend on
    # them — only the file's own helper lemmas live there.
    local_ns = set(re.findall(r"^namespace\s+(\S+)", body, re.M))
    open_ctx = [
        o.strip()
        for o in opens
        if " in" not in o and o.strip() not in local_ns
    ]

    m = re.search(
        r"^theorem\s+(imo[\w']*)\b((?:.|\n)*?):=\s*((?:.|\n)*)", body, re.M
    )
    if not m:
        return None
    name, stmt, proof = m.group(1), m.group(2), m.group(3)

    # The proof runs to the end of the file, minus any trailing `end`s.
    proof = re.sub(r"\n\s*end\s+\w+\s*$", "", proof.rstrip()).rstrip()

    # Everything before the headline theorem: helper lemmas, defs, namespaces.
    preamble = body[: m.start()].rstrip()

    return {
        "file": path.name,
        "name": name,
        "statement": " ".join(stmt.split()),
        "proof": proof,
        "preamble": preamble,
        "opens": open_ctx,
    }


def benchmark_statement(c: dict) -> str:
    """The exact string the prover will be given: standalone, no helpers."""
    opens = " ".join(f"open {o} in" for o in c["opens"])
    stmt = c["statement"]
    return f"{opens} theorem {c['name']} {stmt} := by".strip()


async def verify(worker: LeanWorker, c: dict) -> tuple[bool, str]:
    # --- 1. does Mathlib's own proof still close here? ---
    full = f"{c['preamble']}\n\ntheorem {c['name']} {c['statement']} := {c['proof']}"
    try:
        resp = await worker._send({"cmd": full, "env": worker._base_env}, timeout=180.0)
    except Exception as e:
        return False, f"proof replay raised: {type(e).__name__}"
    errs = [
        m for m in resp.get("messages", []) if m.get("severity") == "error"
    ]
    if "message" in resp and "sorries" not in resp:
        return False, f"proof replay error: {resp['message'][:120]}"
    if errs:
        return False, f"proof replay error: {errs[0].get('data','')[:120]}"
    if resp.get("sorries"):
        return False, "proof replay left sorries"

    # --- 2. does the standalone benchmark form elaborate to an open goal? ---
    bench = benchmark_statement(c)
    try:
        resp2 = await worker._send(
            {"cmd": bench + "\n  sorry", "env": worker._base_env}, timeout=120.0
        )
    except Exception as e:
        return False, f"benchmark form raised: {type(e).__name__}"
    if "message" in resp2 and "sorries" not in resp2:
        return False, f"benchmark form error: {resp2['message'][:120]}"
    hard_errs = [
        m for m in resp2.get("messages", [])
        if m.get("severity") == "error"
        and "declaration uses 'sorry'" not in m.get("data", "")
    ]
    if hard_errs:
        return False, f"benchmark form error: {hard_errs[0].get('data','')[:120]}"
    if not resp2.get("sorries"):
        return False, "benchmark form produced no open goal"

    return True, "ok"


async def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--only", default=None, help="comma-separated file stems")
    ap.add_argument("--out", default="/tmp/imo_verified.json")
    args = ap.parse_args(argv)

    files = sorted(ARCHIVE.glob("*.lean"))
    if args.only:
        want = {s.strip() for s in args.only.split(",")}
        files = [f for f in files if f.stem in want]

    cands = [c for c in (parse_file(f) for f in files) if c]
    # Only statements that don't reference a definition local to their file.
    keep = []
    for c in cands:
        local = set(
            re.findall(
                r"^\s*(?:private\s+)?(?:def|abbrev|structure|inductive)\s+(\w+)",
                c["preamble"], re.M,
            )
        )
        if any(re.search(rf"\b{re.escape(d)}\b", c["statement"]) for d in local):
            continue
        keep.append(c)
    if args.limit:
        keep = keep[: args.limit]

    print(f"{len(keep)} candidate(s) to verify\n", flush=True)

    ex = SubprocessExecutor()
    print("Starting Lean worker (loading Mathlib)...", end=" ", flush=True)
    await ex.start()
    print("ready.\n", flush=True)
    worker = ex._worker if hasattr(ex, "_worker") else ex.worker

    verified = []
    try:
        for c in keep:
            ok, why = await verify(worker, c)
            print(f"  {'PASS' if ok else 'FAIL'}  {c['file']:<18} {c['name']:<18} {'' if ok else why}", flush=True)
            if ok:
                c["benchmark"] = benchmark_statement(c)
                verified.append(c)
    finally:
        await ex.close()

    Path(args.out).write_text(json.dumps(verified, indent=2))
    print(f"\n{len(verified)}/{len(keep)} verified -> {args.out}")
    return 0


if __name__ == "__main__":
    sys.exit(asyncio.run(main()))
