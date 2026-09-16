"""Attempt 0 for the sample: does the row verify with no edit at all?

Writes one row per solution to baseline.jsonl. This is not a gate and it
writes only inside batches/verify-sample/, so it cannot touch
data/verification.jsonl.
"""
import json, re, shutil, subprocess, sys
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
DAFNY = shutil.which("dafny") or "/root/.dotnet/tools/dafny"
SOLVER = shutil.which("z3") or "/usr/local/bin/z3"

KINDS = [("index out of range","index-out-of-range"),
         ("sequence size might be negative","negative-seq-size"),
         ("possible division by zero","division-by-zero"),
         ("decreases expression might not decrease","termination"),
         ("cannot prove termination","termination"),
         ("element might not be in domain","map-domain"),
         ("value does not satisfy the subset constraints","subset-constraint"),
         ("precondition","precondition"),
         ("assertion might not hold","assertion")]

def classify(o):
    for n,k in KINDS:
        if n in o: return k
    return "other"

def one(rec):
    p = ROOT / rec["path"]
    try:
        r = subprocess.run([DAFNY,"verify",str(p),"--solver-path",SOLVER,
                            "--verification-time-limit","30"],
                           capture_output=True, text=True, timeout=300)
        out = r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        return {**rec, "verified": False, "kind": "verifier-timeout", "errors": []}
    ok = r.returncode == 0 and "0 errors" in out
    errs = [l.strip()[:300] for l in out.splitlines() if "Error:" in l]
    return {**rec, "verified": ok, "kind": None if ok else classify(out),
            "errors": errs[:6], "n_errors": len(errs)}

if __name__ == "__main__":
    recs = [json.loads(l) for l in open(HERE/"manifest.jsonl")]
    with ProcessPoolExecutor(max_workers=6) as ex:
        rows = list(ex.map(one, recs, chunksize=1))
    with open(HERE/"baseline.jsonl","w") as f:
        for r in rows: f.write(json.dumps(r)+"\n")
    ok = sum(r["verified"] for r in rows)
    from collections import Counter
    print(f"RESULT verified={ok}/{len(rows)}")
    for k,n in Counter(r["kind"] for r in rows if not r["verified"]).most_common():
        print(f"  {k:<22} {n}")
