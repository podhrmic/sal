#!/usr/bin/env python3
"""Performance benchmark: run every golden-suite case through both the
original SAL 3.3 binaries (.oracle/) and the Rust implementation
(target/release/), measure wall time, and compare.

Results go to tests/golden/bench.jsonl; a summary is printed.

Env: BENCH_TIMEOUT (default 60s), BENCH_JOBS (default 4).
"""

import json
import os
import re
import statistics
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(os.environ.get("SAL_RS_ROOT", Path(__file__).resolve().parent.parent))
RUST_BIN = ROOT / "target" / "release"
ORACLE_BIN = ROOT / ".oracle" / "sal-3.3" / "bin"
MANIFEST = ROOT / "tests" / "golden" / "manifest.jsonl"
OUT = ROOT / "tests" / "golden" / "bench.jsonl"

TOOLS = ["sal-wfc", "sal-smc", "sal-deadlock-checker", "sal-bmc", "sal-inf-bmc",
         "sal-path-finder"]
TIMEOUT = int(os.environ.get("BENCH_TIMEOUT", "60"))
JOBS = int(os.environ.get("BENCH_JOBS", "4"))

# extra benchmark cases: sal-atg on the synthetic examples
ATG_CASES = [
    {"cwd": "tests/atg", "cmd": "sal-atg stopwatch clock stopwatch_goals.scm -ed 5 -id 101 --latching"},
    {"cwd": "tests/atg", "cmd": "sal-atg traffic controller traffic_goals.scm -ed 8 -id 8"},
    {"cwd": "tests/atg", "cmd": "sal-atg gear scheduler gear_goals.scm -ed 8 -id 8"},
    {"cwd": "tests/atg", "cmd": "sal-atg gear scheduler gear_goals.scm -ed 0 -id 8"},
    {"cwd": "tests/atg", "cmd": "sal-atg boundary acc boundary_goals.scm -ed 8 -id 20"},
]


def classify(tool: str, rc: int, out: str) -> str:
    low = out.lower()
    if rc in (124, 125, 137, 143) and not out.strip():
        return "timeout"
    if "k-induction rule failed" in low:
        return "induction_failed"
    if "counterexample:" in low:
        return "counterexample"
    if re.search(r"^proved\.", out, re.MULTILINE):
        return "proved"
    if "no counterexample between depths" in low:
        return "no_ce"
    if tool == "sal-wfc" and re.search(r"^Ok\.", out, re.MULTILINE):
        return "ok"
    if "does not contain deadlock states" in low:
        return "no_deadlock"
    if "deadlock states" in low:
        return "deadlock"
    if "tests generated" in low:
        return "tests"
    if tool.startswith("sal-path") and re.search(r"^Step \d+:", out, re.MULTILINE):
        return "path"
    if rc != 0 or "error" in low:
        return "error"
    return "unknown"


def run_one(bindir: Path, extra_env: dict, cwd: Path, cmd: str, tool: str):
    env = dict(os.environ)
    env.update(extra_env)
    start = time.monotonic()
    try:
        p = subprocess.run(
            ["timeout", "-k", "5", str(TIMEOUT), "bash", "-c",
             f"{bindir}/{cmd}"],
            cwd=cwd, env=env, capture_output=True, text=True,
            timeout=TIMEOUT + 30,
        )
        rc, out = p.returncode, p.stdout + "\n" + p.stderr
    except subprocess.TimeoutExpired:
        rc, out = 124, ""
    elapsed = time.monotonic() - start
    return elapsed, classify(tool, rc, out)


def bench_case(case):
    tool = case["cmd"].split()[0]
    cwd = ROOT / case["cwd"]
    # the oracle needs its own bin dir on PATH (bundled yices 1)
    oracle_env = {"PATH": f"{ORACLE_BIN}:{os.environ['PATH']}"}
    t_oracle, v_oracle = run_one(ORACLE_BIN, oracle_env, cwd, case["cmd"], tool)
    t_rust, v_rust = run_one(RUST_BIN, {}, cwd, case["cmd"], tool)
    return {
        "cwd": case["cwd"],
        "cmd": case["cmd"],
        "tool": tool,
        "oracle_s": round(t_oracle, 3),
        "rust_s": round(t_rust, 3),
        "oracle_verdict": v_oracle,
        "rust_verdict": v_rust,
    }


def fmt_time(s: float) -> str:
    return f"{s:8.2f}s"


def main() -> int:
    recs = [json.loads(l) for l in MANIFEST.read_text().splitlines()]
    cases = [
        {"cwd": r["cwd"], "cmd": r["cmd"]}
        for r in recs
        if r["cmd"].split()[0] in TOOLS and "lsal" not in r["cwd"]
    ]
    cases += ATG_CASES
    print(f"{len(cases)} cases, timeout {TIMEOUT}s, {JOBS} workers", flush=True)

    results = []
    with ThreadPoolExecutor(JOBS) as ex:
        for i, r in enumerate(ex.map(bench_case, cases), 1):
            results.append(r)
            if i % 50 == 0:
                print(f"  ... {i}/{len(cases)}", flush=True)
    with OUT.open("w") as f:
        for r in results:
            f.write(json.dumps(r) + "\n")

    # ---- summary ----
    # comparable = both sides produced the same non-timeout verdict
    comp = [r for r in results
            if r["oracle_verdict"] == r["rust_verdict"]
            and r["oracle_verdict"] not in ("timeout",)]
    print()
    print("=" * 72)
    print("SUMMARY (cases where both implementations agree on the verdict)")
    print("=" * 72)
    by_tool = {}
    for r in comp:
        by_tool.setdefault(r["tool"], []).append(r)
    print(f"{'tool':<22}{'n':>5}{'oracle total':>14}{'rust total':>14}{'speedup':>10}")
    total_o = total_r = 0.0
    for tool in sorted(by_tool):
        rs = by_tool[tool]
        o = sum(r["oracle_s"] for r in rs)
        ru = sum(r["rust_s"] for r in rs)
        total_o += o
        total_r += ru
        sp = o / ru if ru > 0 else float("inf")
        print(f"{tool:<22}{len(rs):>5}{o:>13.1f}s{ru:>13.1f}s{sp:>9.1f}x")
    sp = total_o / total_r if total_r > 0 else float("inf")
    print("-" * 72)
    print(f"{'TOTAL':<22}{len(comp):>5}{total_o:>13.1f}s{total_r:>13.1f}s{sp:>9.1f}x")

    ratios = [r["oracle_s"] / r["rust_s"] for r in comp if r["rust_s"] > 0.001]
    if ratios:
        print()
        print(f"median speedup: {statistics.median(ratios):.1f}x   "
              f"geometric mean: {statistics.geometric_mean(ratios):.1f}x")
        wins = sum(1 for x in ratios if x > 1)
        print(f"rust faster on {wins}/{len(ratios)} comparable cases")

    # where each side times out while the other answers
    o_to = [r for r in results if r["oracle_verdict"] == "timeout"
            and r["rust_verdict"] != "timeout"]
    r_to = [r for r in results if r["rust_verdict"] == "timeout"
            and r["oracle_verdict"] != "timeout"]
    print()
    print(f"oracle times out, rust answers: {len(o_to)} cases")
    print(f"rust times out, oracle answers: {len(r_to)} cases")

    # extremes among comparable
    comp_slow = sorted(comp, key=lambda r: r["oracle_s"] - r["rust_s"])
    print()
    print("largest rust wins (oracle_s -> rust_s):")
    for r in comp_slow[-5:][::-1]:
        print(f"  {r['oracle_s']:7.2f}s -> {r['rust_s']:6.2f}s  {r['cmd'][:60]} ({r['cwd'].split('/')[-1]})")
    print("largest rust losses:")
    for r in comp_slow[:5]:
        if r["rust_s"] > r["oracle_s"]:
            print(f"  {r['oracle_s']:7.2f}s -> {r['rust_s']:6.2f}s  {r['cmd'][:60]} ({r['cwd'].split('/')[-1]})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
