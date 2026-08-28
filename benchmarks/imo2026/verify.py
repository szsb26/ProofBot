#!/usr/bin/env python3
import argparse, json, pathlib, random, urllib.request

parser = argparse.ArgumentParser()
parser.add_argument("--no-cache", action="store_true")
args = parser.parse_args()

URL = "https://axle.axiommath.ai/api/v1/verify_proof"

for q in ["Q1", "Q2", "Q3", "Q4", "Q5", "Q6"]:
    d = pathlib.Path("IMO2026") / q
    payload = {
        "formal_statement": (d / "problem.lean").read_text(encoding="utf-8"),
        "content": (d / "solution.lean").read_text(encoding="utf-8"),
        "mathlib_options": False,
        "use_def_eq": True,
        "verify_negation": False,
        "ignore_imports": True,
        "environment": "lean-4.31.0",
        "timeout_seconds": 900,
    }
    if args.no_cache:
        payload["anti_cache"] = random.getrandbits(64)
    req = urllib.request.Request(
        URL,
        data=json.dumps(payload).encode(),
        headers={"Content-Type": "application/json"},
    )
    okay = json.load(urllib.request.urlopen(req))["okay"]
    print(f"{q}: okay={okay} {'(passed)' if okay else '(failed)'}")
