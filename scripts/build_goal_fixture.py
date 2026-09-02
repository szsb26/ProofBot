#!/usr/bin/env python3
"""
Distil tests/fixtures/lean_goals.jsonl from recorded REPL logs.

The goal-rendering tests must not be written by hand. A hand-written mock
encodes what we BELIEVE Lean returns, and that belief was wrong for months:
`_parse_goal_string` corrupted 890 of 3704 real goals (deleting hypotheses
whose type wrapped, truncating wrapped targets, promoting continuation lines
to invented hypotheses) while every unit test passed, because the tests fed
it single-line goals it could handle.

So the fixture is sampled from goals Lean actually emitted, deliberately
weighted toward the shapes that broke it. traces/ is gitignored, so the
sample is committed and this script regenerates it:

    python scripts/build_goal_fixture.py
"""
import json, glob, re, sys
from pathlib import Path

ROOT = Path(__file__).parent.parent
OUT = ROOT / "tests" / "fixtures" / "lean_goals.jsonl"
PER_SHAPE = 12          # keep the fixture reviewable by hand
MAX_CHARS = 1200        # skip pathologically huge goals


def shapes(g: str) -> list[str]:
    """Which known-difficult renderings does this goal exercise?"""
    lines = [l.rstrip() for l in g.split("\n")]
    ti = next((i for i, l in enumerate(lines) if l.startswith("⊢")), None)
    out = []
    if any(l.strip().endswith(":") and not l.startswith("⊢") for l in lines):
        out.append("wrapped_hypothesis")     # the old parser deleted these
    if ti is not None and ti + 1 < len(lines):
        out.append("wrapped_target")         # the old parser truncated these
    if any(" : " in l and (l.startswith((" ", "\t")) or (ti is not None and i > ti))
           for i, l in enumerate(lines)):
        out.append("continuation_with_colon")  # the old parser invented these
    if lines and lines[0].startswith("case "):
        out.append("case_label")
    if "✝" in g:
        out.append("inaccessible_name")
    if not out:
        out.append("plain")
    return out


def main() -> int:
    seen, picked, counts = set(), [], {}
    for f in sorted(glob.glob(str(ROOT / "traces" / "*" / "lean" / "*.jsonl"))):
        run = Path(f).parts[-3]
        for line in open(f, encoding="utf-8"):
            try:
                r = json.loads(line)
            except json.JSONDecodeError:
                continue
            resp = r.get("response")
            if not isinstance(resp, dict):
                continue
            for g in resp.get("goals") or []:
                if not isinstance(g, str):
                    continue
                g = g.strip()
                if not g or g in seen or len(g) > MAX_CHARS:
                    continue
                sh = shapes(g)
                if all(counts.get(s, 0) >= PER_SHAPE for s in sh):
                    continue
                seen.add(g)
                for s in sh:
                    counts[s] = counts.get(s, 0) + 1
                picked.append({"run": run, "seq": r.get("seq"), "shapes": sh, "goal": g})
    if not picked:
        print("no recorded goals found — run an eval with --trace first", file=sys.stderr)
        return 1
    OUT.parent.mkdir(parents=True, exist_ok=True)
    with open(OUT, "w", encoding="utf-8") as fh:
        for row in picked:
            fh.write(json.dumps(row, ensure_ascii=False) + "\n")
    print(f"wrote {len(picked)} recorded goals to {OUT.relative_to(ROOT)}")
    for s, n in sorted(counts.items()):
        print(f"   {s:<26}{n}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
