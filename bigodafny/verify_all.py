"""Run `dafny verify` on every translation and split the safe from the unproven.

Passing the tests shows a translation works on the inputs BigOBench stored.
`dafny verify` asks a different question: are the obligations Dafny raises on
its own discharged for EVERY input? Those exist with no pre/postcondition
written -- indexing a seq, dividing, and terminating are each a proof
obligation.

A failure here is not a failing test. It means the translation may fault on an
input outside the stored set, and nothing in the test gate would notice.
"""
from __future__ import annotations
import argparse, re, shutil, subprocess, sys
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

from common import (DATA, INEXACT, ROOT, SOLUTIONS, event, log, write_json,
                    write_jsonl)

DAFNY = shutil.which("dafny") or "/root/.dotnet/tools/dafny"
SOLVER = shutil.which("z3") or "/usr/local/bin/z3"
UNVERIFIED = ROOT / "solutions-unverified"

# Dafny reports these against code with no user-written specification at all.
KINDS = [
    ("index out of range", "index-out-of-range"),
    ("sequence size might be negative", "negative-seq-size"),
    ("possible division by zero", "division-by-zero"),
    ("decreases expression might not decrease", "termination"),
    ("cannot prove termination", "termination"),
    ("element might not be in domain", "map-domain"),
    ("value does not satisfy the subset constraints", "subset-constraint"),
    ("precondition", "precondition"),
    ("assertion might not hold", "assertion"),
]


def classify(out):
    for needle, kind in KINDS:
        if needle in out:
            return kind
    return "other"


def one(path_str):
    p = Path(path_str)
    try:
        r = subprocess.run(
            [DAFNY, "verify", str(p), "--solver-path", SOLVER,
             "--verification-time-limit", "30"],
            capture_output=True, text=True, timeout=180)
        out = (r.stdout + r.stderr)
    except subprocess.TimeoutExpired:
        return {"solution_id": p.stem, "path": str(p.relative_to(ROOT)),
                "verified": False, "kind": "verifier-timeout", "detail": ""}
    ok = r.returncode == 0 and "0 errors" in out
    errs = [l for l in out.splitlines() if re.search(r"Error:", l)]
    return {"solution_id": p.stem, "path": str(p.relative_to(ROOT)),
            "verified": ok,
            "kind": None if ok else classify(out),
            "error_count": len(errs),
            "detail": "" if ok else (errs[0][:200] if errs else out.strip()[-200:])}


def run(dirs, workers=8, move=False):
    files = [str(f) for d in dirs for f in sorted(d.rglob("*.dfy"))
             if "TODO: translate" not in f.read_text(encoding="utf-8")]
    log(f"verifying {len(files)} translations across {len(dirs)} directories")
    with ProcessPoolExecutor(max_workers=workers) as ex:
        rows = list(ex.map(one, files, chunksize=1))
    rows.sort(key=lambda r: (int(r["solution_id"].split("_")[0]), r["solution_id"]))
    write_jsonl(DATA / "verification.jsonl", rows)

    ok = sum(r["verified"] for r in rows)
    kinds = Counter(r["kind"] for r in rows if not r["verified"])
    summary = {"total": len(rows), "verified": ok, "unverified": len(rows) - ok,
               "kinds": dict(kinds.most_common())}
    write_json(DATA / "verification_summary.json", summary)
    event("verify_all", **summary)
    log(f"verified {ok}/{len(rows)}")
    for k, n in kinds.most_common():
        log(f"  {k:<22} {n}")

    if move:
        moved = 0
        for r in rows:
            if r["verified"]:
                continue
            src = ROOT / r["path"]
            if not src.exists() or src.parent.parent == UNVERIFIED:
                continue
            dst = UNVERIFIED / src.parent.name / src.name
            dst.parent.mkdir(parents=True, exist_ok=True)
            subprocess.run(["git", "mv", str(src), str(dst)], cwd=ROOT.parent,
                           check=False, capture_output=True)
            moved += 1
        log(f"moved {moved} unverified translations to {UNVERIFIED.name}/")
    return rows


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--move", action="store_true")
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--inexact", action="store_true",
                    help="also verify solutions-inexact/")
    a = ap.parse_args()
    dirs = [SOLUTIONS] + ([INEXACT] if a.inexact else [])
    run([d for d in dirs if d.exists()], workers=a.workers, move=a.move)
