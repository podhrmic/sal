#!/usr/bin/env python3
"""Generate the golden verdict manifest by running the SAL 3.3 oracle.

Test cases come from two sources:
  1. README files in the corpus: every suggested `sal-*` command line
     (these encode correct context parameters and lemma chains).
  2. Auto-enumeration: for every .sal file, a `sal-wfc` run; for every
     assertion in an unparameterized context, `sal-smc` and `sal-bmc -d 10`
     runs; for every module, a `sal-deadlock-checker` run.

Each case is executed with a timeout; stdout/stderr are classified into a
verdict. Results go to tests/golden/manifest.jsonl (one JSON object per
line). The script is resumable: cases whose key already appears in the
manifest are skipped.
"""

import json
import os
import re
import shlex
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CORPUS = ROOT / "tests" / "corpus"
MANIFEST = ROOT / "tests" / "golden" / "manifest.jsonl"
ORACLE_BIN = ROOT / ".oracle" / "sal-3.3" / "bin"
TIMEOUT = int(os.environ.get("GOLDEN_TIMEOUT", "60"))
JOBS = int(os.environ.get("GOLDEN_JOBS", "4"))

TOOLS = {
    "sal-wfc", "sal-smc", "sal-bmc", "sal-inf-bmc",
    "sal-deadlock-checker", "sal-path-finder", "sal-path-explorer",
}

ASSERTION_RE = re.compile(
    r"^\s*([A-Za-z][A-Za-z0-9_?]*)\s*:\s*(THEOREM|LEMMA|CLAIM|OBLIGATION)\b",
    re.MULTILINE,
)
MODULE_RE = re.compile(
    r"^\s*([A-Za-z][A-Za-z0-9_?]*)\s*(\[[^\]]*\])?\s*:\s*MODULE\s*=",
    re.MULTILINE,
)
# context header: name { params } : CONTEXT =
CONTEXT_RE = re.compile(
    r"^\s*([A-Za-z][A-Za-z0-9_?]*)\s*(\{[^}]*\})?\s*:\s*CONTEXT\s*=",
    re.MULTILINE,
)


def strip_comments(text: str) -> str:
    return re.sub(r"%[^\n]*", "", text)


def readme_cases():
    for readme in sorted(CORPUS.rglob("README")):
        for line in readme.read_text(errors="replace").splitlines():
            line = line.strip().lstrip("%>").strip()
            if not line or not line.split()[0] in TOOLS:
                continue
            if " -s uclid" in line or "--solver" in line:
                continue  # solvers we do not ship
            # normalize verbosity flags out of the key/command
            line = re.sub(r"\s-v\s+\d+", "", line)
            yield {
                "kind": "readme",
                "cwd": str(readme.parent.relative_to(ROOT)),
                "cmd": line,
            }


def auto_cases():
    for sal in sorted(CORPUS.rglob("*.sal")):
        rel = str(sal.parent.relative_to(ROOT))
        name = sal.stem
        yield {"kind": "auto", "cwd": rel, "cmd": f"sal-wfc {sal.name}"}
        text = strip_comments(sal.read_text(errors="replace"))
        m = CONTEXT_RE.search(text)
        if m is None or m.group(2):
            continue  # parameterized (or unparsable) context: README-only
        for am in ASSERTION_RE.finditer(text):
            a = am.group(1)
            yield {"kind": "auto", "cwd": rel, "cmd": f"sal-smc {name} {a}"}
            yield {"kind": "auto", "cwd": rel,
                   "cmd": f"sal-bmc -d 10 {name} {a}"}
        for mm in MODULE_RE.finditer(text):
            if mm.group(2):
                continue  # parameterized module
            yield {"kind": "auto", "cwd": rel,
                   "cmd": f"sal-deadlock-checker {name} {mm.group(1)}"}


def classify(tool: str, rc: int, out: str) -> dict:
    v: dict = {}
    low = out.lower()
    # 124 = timeout; 125/137/143 seen when `timeout` kills the sh wrapper
    # scripts the SAL tools use.
    if rc == 124 or (rc in (125, 137, 143) and not out.strip()):
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
    elif tool.startswith("sal-path") and re.search(r"^Step \d+:", out, re.MULTILINE):
        v["verdict"] = "path"
        v["path_steps"] = len(re.findall(r"^Step \d+:", out, re.MULTILINE))
    elif rc != 0 or "error" in low:
        v["verdict"] = "error"
    else:
        v["verdict"] = "unknown"
    return v


def run_case(case: dict) -> dict:
    env = dict(os.environ, PATH=f"{ORACLE_BIN}:{os.environ['PATH']}")
    argv = shlex.split(case["cmd"])
    tool = argv[0]
    try:
        p = subprocess.run(
            ["timeout", "-k", "5", str(TIMEOUT)] + argv,
            cwd=ROOT / case["cwd"], env=env,
            capture_output=True, text=True, timeout=TIMEOUT + 30,
        )
        rc, out = p.returncode, p.stdout + "\n" + p.stderr
    except subprocess.TimeoutExpired:
        rc, out = 124, ""
    rec = dict(case)
    rec.update(classify(tool, rc, out))
    rec["exit"] = rc
    tail = [l for l in out.strip().splitlines() if l.strip()][-3:]
    rec["raw_tail"] = tail
    return rec


def main():
    MANIFEST.parent.mkdir(parents=True, exist_ok=True)
    done = set()
    if MANIFEST.exists():
        for line in MANIFEST.read_text().splitlines():
            try:
                r = json.loads(line)
                done.add((r["cwd"], r["cmd"]))
            except json.JSONDecodeError:
                pass

    cases, seen = [], set(done)
    for c in list(readme_cases()) + list(auto_cases()):
        key = (c["cwd"], c["cmd"])
        if key not in seen:
            seen.add(key)
            cases.append(c)

    print(f"{len(cases)} new cases (of {len(seen)} total), "
          f"timeout={TIMEOUT}s, jobs={JOBS}")
    with MANIFEST.open("a") as f, ThreadPoolExecutor(JOBS) as ex:
        for i, rec in enumerate(ex.map(run_case, cases), 1):
            f.write(json.dumps(rec) + "\n")
            f.flush()
            print(f"[{i}/{len(cases)}] {rec['verdict']:>15}  "
                  f"({rec['cwd']}) {rec['cmd']}")
    print("done")


if __name__ == "__main__":
    sys.exit(main())
