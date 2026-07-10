#!/usr/bin/env python3
"""Differential testing of sal-wfc: mutate corpus files and compare
accept/reject verdicts between the oracle and the Rust implementation.

Mutations are simple textual edits likely to produce type/name errors (or
remain well-formed — both outcomes are informative).
"""

import json
import os
import random
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ORACLE = ROOT / ".oracle" / "sal-3.3" / "bin" / "sal-wfc"
OURS = ROOT / "target" / "debug" / "sal-wfc"
CORPUS = ROOT / "tests" / "corpus" / "dist"

N_MUTANTS = int(os.environ.get("N_MUTANTS", "150"))
SEED = int(os.environ.get("SEED", "1"))


def mutate(src: str, rng: random.Random) -> str | None:
    lines = src.splitlines(keepends=True)
    kind = rng.choice(["rename_use", "num_for_bool", "bool_for_num", "swap_cmp",
                       "delete_decl_char", "shuffle_ident"])
    idxs = list(range(len(lines)))
    rng.shuffle(idxs)
    for i in idxs:
        l = lines[i]
        if l.strip().startswith("%"):
            continue
        if kind == "rename_use":
            m = re.search(r"\b([a-z][A-Za-z0-9_]{2,})\b", l)
            if m and m.group(1) not in ("and", "or", "not", "xor", "div", "mod"):
                lines[i] = l[: m.start()] + m.group(1) + "_zqx" + l[m.end():]
                return "".join(lines)
        elif kind == "num_for_bool":
            m = re.search(r"\bTRUE\b|\bFALSE\b", l)
            if m:
                lines[i] = l[: m.start()] + "42" + l[m.end():]
                return "".join(lines)
        elif kind == "bool_for_num":
            m = re.search(r"(?<![\w.])(\d+)(?![\w.])", l)
            if m and ".." not in l:
                lines[i] = l[: m.start()] + "TRUE" + l[m.end():]
                return "".join(lines)
        elif kind == "swap_cmp":
            if " = " in l and "--" not in l:
                lines[i] = l.replace(" = ", " + ", 1)
                return "".join(lines)
        elif kind == "delete_decl_char":
            m = re.search(r"\bOUTPUT\b", l)
            if m:
                lines[i] = l[: m.start()] + "INPUT" + l[m.end():]
                return "".join(lines)
        elif kind == "shuffle_ident":
            m = re.search(r"\b([A-Z][A-Za-z0-9_]{3,})\b", l)
            if m and m.group(1).upper() != m.group(1):
                lines[i] = l[: m.start()] + m.group(1)[::-1] + l[m.end():]
                return "".join(lines)
    return None


def verdict(binary: Path, path: Path, cwd: Path) -> str:
    try:
        p = subprocess.run(
            [str(binary), path.name],
            cwd=cwd,
            capture_output=True,
            text=True,
            timeout=30,
        )
        return "ok" if p.returncode == 0 else "error"
    except subprocess.TimeoutExpired:
        return "timeout"


def main() -> int:
    rng = random.Random(SEED)
    files = sorted(CORPUS.rglob("*.sal"))
    # only mutate files both tools accept unmutated
    base_ok = []
    for f in files:
        if verdict(ORACLE, f, f.parent) == "ok":
            base_ok.append(f)
    print(f"{len(base_ok)} oracle-accepted base files")

    divergences = []
    tested = 0
    while tested < N_MUTANTS:
        f = rng.choice(base_ok)
        src = f.read_text(errors="replace")
        mutated = mutate(src, rng)
        if mutated is None or mutated == src:
            continue
        tested += 1
        with tempfile.TemporaryDirectory() as td:
            # keep sibling contexts visible: write mutant into the same dir
            # layout under a temp root, with the ORIGINAL directory on the
            # context path via symlinks
            tdir = Path(td)
            for sib in f.parent.iterdir():
                if sib.is_file():
                    (tdir / sib.name).symlink_to(sib)
            mpath = tdir / f.name
            mpath.unlink(missing_ok=True)
            mpath.write_text(mutated)
            vo = verdict(ORACLE, mpath, tdir)
            vr = verdict(OURS, mpath, tdir)
            if vo != vr:
                keep = ROOT / "tests" / "regressions" / f"wfc-{tested}-{f.stem}.sal"
                keep.parent.mkdir(parents=True, exist_ok=True)
                keep.write_text(mutated)
                divergences.append((f.name, vo, vr, str(keep)))
                print(f"DIVERGE {f.name}: oracle={vo} ours={vr} -> {keep}")
    print(f"{tested} mutants tested, {len(divergences)} divergences")
    return 1 if divergences else 0


if __name__ == "__main__":
    sys.exit(main())
