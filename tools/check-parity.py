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

IMPLEMENTED = ["sal-wfc", "sal-smc", "sal-deadlock-checker"]
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


def main() -> int:
    tools = sys.argv[1:] or IMPLEMENTED
    recs = [json.loads(l) for l in MANIFEST.read_text().splitlines()]
    total = ok = 0
    mismatches = []
    for r in recs:
        tool = r["cmd"].split()[0]
        if tool not in tools:
            continue
        if "lsal" in r["cwd"]:
            continue  # lsal front-end is out of scope for now
        total += 1
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
        ours = classify(tool, rc, out)
        want = r["verdict"]
        got = ours["verdict"]
        match = got == want
        # counterexample depth comparison when both have it
        detail = ""
        if match and want == "counterexample" and "ce_steps" in r:
            if ours.get("ce_steps") != r["ce_steps"]:
                match = False
                detail = f" (steps: want {r['ce_steps']}, got {ours.get('ce_steps')})"
        if match:
            ok += 1
        else:
            tail = " | ".join(l for l in out.strip().splitlines()[-2:])[:110]
            mismatches.append(
                f"({r['cwd']}) {r['cmd']}: want={want} got={got}{detail} :: {tail}"
            )
    print(f"{ok}/{total} verdicts match")
    for m in mismatches:
        print("MISMATCH", m)
    return 0 if ok == total else 1


if __name__ == "__main__":
    sys.exit(main())
