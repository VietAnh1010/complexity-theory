"""Re-verify every complexity proof and record it against BigOBench's label.

A file in solutions-proved/ claims two things: it behaves like its Python
(tests), and its step count obeys a proved bound (dafny verify). This re-checks
the second from scratch and tabulates the bound against the label.

A disagreement is a finding, not an error. BigOBench's label is a regression
over profiling runs; a proved bound holds for every input. Where they conflict,
the proof is the stronger statement.
"""
from __future__ import annotations
import re, shutil, subprocess, sys

from common import (DAFNY_VERSION, DATA, UNSCREENED, PROVED_NLOGN, SOLUTIONS, UNVERIFIED,
                    PROVED, event, log, read_jsonl, write_jsonl, DISPUTED,
                    UNGATEABLE)

DAFNY = shutil.which("dafny") or "/root/.dotnet/tools/dafny"
SOLVER = shutil.which("z3") or "/usr/local/bin/z3"


def bound_of(text):
    """The bound `Solve` promises, not whichever `ensures` comes first.

    Three defects this replaces, all found on 2026-09-21/22 and none of them
    affecting a verdict -- `verified` comes from Dafny, never from here -- but
    all of them publishing a wrong bound:

      * the first `ensures steps <=` in the file is a HELPER's when one is
        declared before Solve. 7 of 151 proofs recorded a helper's bound;
        2496_30 published `6100` for a row whose Solve is O(n**2), and
        2803_133 published Fact's bound rather than Solve's.
      * a wrapped `ensures` was cut at the first newline. 1243_0 published
        only its first term until the source was reflowed onto one line.
      * a two-clause `ensures` (`c >= 1 ==> steps <= ...` guarded, plus the
        `c < 1` case) matched neither pattern and recorded null. 1738_24,
        2254_6 and 457_27 had no bound on file although all three verify.

    Returns the clauses joined by " AND " when Solve states more than one.
    """
    m = re.search(r"\bmethod\s+Solve\b.*?(?=\n\{)", text, re.S)
    scope = m.group(0) if m else text
    out = []
    for line in scope.splitlines():
        if not re.search(r"\bensures\b", line):
            continue
        # the clause runs to the end of the signature or the next ensures /
        # requires / decreases / modifies, so pull the continuation lines too
        start = scope.index(line)
        rest = scope[start:]
        clause = []
        for j, cl in enumerate(rest.splitlines()):
            if j and re.match(r"\s*(ensures|requires|decreases|modifies|reads)\b", cl):
                break
            clause.append(cl.split("//")[0].rstrip())
        joined = " ".join(x.strip() for x in clause if x.strip())
        hit = re.search(r"ensures\s+(.*?steps\s*<=\s*.+)$", joined)
        if hit:
            clause_text = hit.group(1).strip()
            # keep the old flat format for an unguarded clause, so existing
            # records and anything reading them do not shift under this fix
            out.append(re.sub(r"^steps\s*<=\s*", "", clause_text))
    return " AND ".join(out) if out else None


def scan_assumes():
    """`assume` anywhere in the corpus, not just in the proofs.

    `assume {:axiom} 0 <= idx < |arr|` discharges an index obligation silently:
    the file verifies, and nothing in the summary says why. Two rows in
    solutions/ carried one for several waves because the audits only ever
    grepped solutions-unverified/.
    """
    hits = []
    for d in (SOLUTIONS, UNVERIFIED, UNSCREENED, PROVED, DISPUTED, UNGATEABLE):
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
    # `solutions-proved/nlogn/` is nested inside `solutions-proved/`, so one
    # rglob reaches both; listing the two roots separately would double-count.
    files = sorted(PROVED.rglob("*.dfy")) if PROVED.exists() else []
    for p in files:
        variant = "nlogn" if PROVED_NLOGN in p.parents else "base"
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
            "proof_variant": variant,
            "label": ds.get(sid, {}).get("time_complexity_inferred"),
            "proved_bound": bound_of(text),
            "verified": ok,
            "assume_count": assumes,
            "dafny_version": DAFNY_VERSION,
            "verifier_output": out.strip().splitlines()[-1] if out.strip() else "",
        })
        log(f"  [{variant:>5}] {sid:>10}  {'VERIFIED' if ok else 'FAILED  '}  "
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
