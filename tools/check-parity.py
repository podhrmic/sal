#!/usr/bin/env python3
"""Compare Rust tool verdicts against the golden manifest.

Usage: check-parity.py [tool ...]   (default: all implemented tools)
"""

import json
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(os.environ.get("SAL_RS_ROOT", Path(__file__).resolve().parent.parent))
BIN = ROOT / "target" / os.environ.get("SAL_RS_PROFILE", "debug")
MANIFEST = ROOT / "tests" / "golden" / "manifest.jsonl"

IMPLEMENTED = ["sal-wfc", "sal-smc", "sal-deadlock-checker", "sal-bmc", "sal-inf-bmc", "sal-path-finder"]
TIMEOUT = int(os.environ.get("PARITY_TIMEOUT", "60"))


def classify(tool: str, rc: int, out: str) -> dict:
    v: dict = {}
    low = out.lower()
    if rc in (124, 125, 137, 143) and not out.strip():
        v["verdict"] = "timeout"
    elif "k-induction rule failed" in low:
        v["verdict"] = "induction_failed"
    elif "counterexample:" in low or "counter-example:" in low:
        v["verdict"] = "counterexample"
        steps = re.findall(r"^Step (\d+):", out, re.MULTILINE)
        if steps:
            v["ce_steps"] = len(steps)
    elif re.search(r"^proved\.", out, re.MULTILINE):
        v["verdict"] = "proved"
    elif "no counterexample between depths" in low:
        v["verdict"] = "no_ce"
    elif tool == "sal-wfc" and re.search(r"^Ok\.", out, re.MULTILINE):
        v["verdict"] = "ok"
    elif "does not contain deadlock states" in low:
        v["verdict"] = "no_deadlock"
    elif "deadlock states" in low:
        v["verdict"] = "deadlock"
    elif rc != 0 or "error" in low:
        v["verdict"] = "error"
    else:
        v["verdict"] = "unknown"
    return v


def run_case(r):
    tool = r["cmd"].split()[0]
    argv = r["cmd"].split(None, 1)
    cmd = f"{BIN}/{argv[0]} {argv[1] if len(argv) > 1 else ''}"
    try:
        p = subprocess.run(
            ["timeout", "-k", "5", str(TIMEOUT), "bash", "-c", cmd],
            cwd=ROOT / r["cwd"],
            capture_output=True,
            text=True,
            timeout=TIMEOUT + 30,
        )
        rc, out = p.returncode, p.stdout + "\n" + p.stderr
    except subprocess.TimeoutExpired:
        rc, out = 124, ""
    return r, classify(tool, rc, out), out


def main() -> int:
    from concurrent.futures import ThreadPoolExecutor
    tools = sys.argv[1:] or IMPLEMENTED
    recs = [json.loads(l) for l in MANIFEST.read_text().splitlines()]
    cases = [
        r
        for r in recs
        if r["cmd"].split()[0] in tools and "lsal" not in r["cwd"]
    ]
    total = ok = 0
    mismatches = []
    soft = []
    jobs = int(os.environ.get("PARITY_JOBS", "8"))
    with ThreadPoolExecutor(jobs) as ex:
        results = list(ex.map(run_case, cases))
    for r, ours, out in results:
        total += 1
        want = r["verdict"]
        got = ours["verdict"]
        match = got == want
        # if the oracle itself timed out, any verdict from us is acceptable
        if want == "timeout":
            match = True
        detail = ""
        # counterexample depth compared softly (trace choice may differ)
        if match and want == "counterexample" and "ce_steps" in r:
            if ours.get("ce_steps") != r["ce_steps"]:
                soft.append(
                    f"({r['cwd']}) {r['cmd']}: steps want {r['ce_steps']} got {ours.get('ce_steps')}"
                )
        if match:
            ok += 1
        else:
            tail = " | ".join(l for l in out.strip().splitlines()[-2:])[:110]
            mismatches.append(
                f"({r['cwd']}) {r['cmd']}: want={want} got={got}{detail} :: {tail}"
            )
    print(f"{ok}/{total} verdicts match ({len(soft)} soft step-count diffs)")
    for m in mismatches:
        print("MISMATCH", m)
    for m in soft:
        print("SOFT", m)
    return 0 if ok == total else 1


if __name__ == "__main__":
    sys.exit(main())
