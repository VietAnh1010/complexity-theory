"""Re-verify every complexity proof and record it against BigOBench's label.

A file in solutions-verified/ claims two things: it behaves like its Python
(tests), and its step count obeys a proved bound (dafny verify). This re-checks
the second from scratch and tabulates the bound against the label.

A disagreement is a finding, not an error. BigOBench's label is a regression
over profiling runs; a proved bound holds for every input. Where they conflict,
the proof is the stronger statement.
"""
from __future__ import annotations
import re, shutil, subprocess, sys

from common import (DAFNY_VERSION, DATA, INEXACT, NLOGN, SOLUTIONS, UNVERIFIED,
                    VERIFIED, event, log, read_jsonl, write_jsonl)

DAFNY = shutil.which("dafny") or "/root/.dotnet/tools/dafny"
SOLVER = shutil.which("z3") or "/usr/local/bin/z3"


def bound_of(text):
    m = re.search(r"ensures\s+steps\s*<=\s*(.+?)\s*(?://.*)?$", text, re.M)
    return m.group(1).strip() if m else None


def scan_assumes():
    """`assume` anywhere in the corpus, not just in the proofs.

    `assume {:axiom} 0 <= idx < |arr|` discharges an index obligation silently:
    the file verifies, and nothing in the summary says why. Two rows in
    solutions/ carried one for several waves because the audits only ever
    grepped solutions-unverified/.
    """
    hits = []
    for d in (SOLUTIONS, UNVERIFIED, INEXACT, VERIFIED, NLOGN):
        if not d.exists():
            continue
        for f in sorted(d.rglob("*.dfy")):
            for i, line in enumerate(f.read_text(encoding="utf-8").splitlines(), 1):
                if re.search(r"\bassume\b", line):
                    hits.append((str(f), i, line.strip()))
    for path, i, line in hits:
        log(f"  ASSUME {path}:{i}  {line}")
    log(f"assume scan: {len(hits)} occurrence(s) across the corpus")
    event("assume_scan", count=len(hits))
    return hits


def run():
    ds = {r["solution_id"]: r for r in read_jsonl(DATA / "dataset.jsonl")}
    rows = []
    files = [(d.name, f) for d in (VERIFIED, NLOGN) if d.exists()
             for f in sorted(d.rglob("*.dfy"))]
    for dirname, p in files:
        sid = p.stem
        text = p.read_text(encoding="utf-8")
        r = subprocess.run([DAFNY, "verify", str(p), "--solver-path", SOLVER],
                           capture_output=True, text=True, timeout=600)
        out = (r.stdout + r.stderr)
        ok = r.returncode == 0 and "0 errors" in out
        # A proof that leans on `assume` proves nothing. Count them.
        assumes = len(re.findall(r"\bassume\b", text))
        rows.append({
            "solution_id": sid,
            "dir": dirname,
            "label": ds.get(sid, {}).get("time_complexity_inferred"),
            "proved_bound": bound_of(text),
            "verified": ok,
            "assume_count": assumes,
            "dafny_version": DAFNY_VERSION,
            "verifier_output": out.strip().splitlines()[-1] if out.strip() else "",
        })
        log(f"  [{dirname[10:]:>8}] {sid:>10}  {'VERIFIED' if ok else 'FAILED  '}  "
            f"label={rows[-1]['label']}  bound={rows[-1]['proved_bound']}"
            + ("  ASSUMES!" if assumes else ""))
    write_jsonl(DATA / "complexity_proofs.jsonl", rows)
    n_ok = sum(r["verified"] for r in rows)
    n_assume = sum(1 for r in rows if r["assume_count"])
    log(f"proofs: {n_ok}/{len(rows)} verify; {n_assume} contain `assume`")
    event("proofs", verified=n_ok, total=len(rows), with_assume=n_assume)
    return rows


if __name__ == "__main__":
    rows = run()
    hits = scan_assumes()
    sys.exit(0 if (all(r["verified"] and not r["assume_count"] for r in rows)
                   and not hits) else 1)
