"""Re-verify every complexity proof and record it against BigOBench's label.

A disagreement with the label is a finding, not an error: the label is fitted
from profiling, while a proved bound holds for every input.
"""
from __future__ import annotations
import hashlib, re, subprocess, sys
from concurrent.futures import ThreadPoolExecutor

from common import (WORKERS, DAFNY_VERSION, z3_version, DATA, UNSCREENED, SOLUTIONS, UNVERIFIED,
                    PROVED, PRELUDE, log, read_jsonl, write_jsonl, DISPUTED,
                    UNGATEABLE, UNSURE, ROOT)

# The prove campaign's audit compares a proof with its row; every proof gets it.
sys.path.insert(0, str(ROOT.parent / ".claude/skills/bigodafny-prove-campaign/scripts"))
import audit  # noqa: E402

DAFNY = "dafny"   # on PATH; dafny finds z3 on PATH itself


def bound_of(text):
    """The bound `Solve` promises, not a helper's. Handles wrapped and guarded
    clauses; joins several with " AND "."""
    # skip attributes: `method {:isolate_assertions} Solve` otherwise misses
    # and the whole file becomes the scope, pulling body code into the bound
    m = re.search(r"\bmethod\s+(?:\{:[^}]*\}\s*)*Solve\b.*?(?=\n\{)", text, re.S)
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
            # an unguarded clause keeps the flat format existing records use
            out.append(re.sub(r"^steps\s*<=\s*", "", clause_text))
    return " AND ".join(out) if out else None


def scan_assumes():
    """`assume` anywhere in the corpus, not just in the proofs: it discharges an
    obligation silently."""
    hits = []
    for d in (SOLUTIONS, UNVERIFIED, UNSCREENED, PROVED, DISPUTED, UNGATEABLE, UNSURE):
        if not d.exists():
            continue
        for f in sorted(d.rglob("*.dfy")):
            for i, line in enumerate(f.read_text(encoding="utf-8").splitlines(), 1):
                if re.search(r"\bassume\b", line.split("//")[0]):
                    hits.append((str(f), i, line.strip()))
    for path, i, line in hits:
        log(f"  ASSUME {path}:{i}  {line}")
    log(f"assume scan: {len(hits)} occurrence(s) across the corpus")
    return hits


def changes_row(r):
    return r["same_python"] != "identical" or bool(r["requires_changed"])


def run(workers=WORKERS):
    ds = {r["solution_id"]: r for r in read_jsonl(DATA / "dataset.jsonl")}
    # one rglob also reaches value-bounded/
    files = sorted(PROVED.rglob("*.dfy")) if PROVED.exists() else []
    Z3 = z3_version()
    # A proof's verdict depends only on these inputs; an unchanged, verified
    # proof keeps its record. `--all` re-checks every proof.
    old = {} if "--all" in sys.argv else {
        r["solution_id"]: r for r in read_jsonl(DATA / "complexity_proofs.jsonl")}
    def fingerprint(p):
        h = hashlib.sha256(f"{DAFNY_VERSION} {Z3}".encode())
        for f in [p, PRELUDE, *(f for d in (SOLUTIONS, UNVERIFIED, UNSCREENED, DISPUTED,
                                            UNGATEABLE, UNSURE) for f in d.glob(f"*/{p.stem}.dfy"))]:
            h.update(f.read_bytes())
        return h.hexdigest()[:16]
    def check(p):
        sid = p.stem
        if not p.exists():      # removed mid-run, e.g. by a campaign agent
            return None
        fp = fingerprint(p)
        prev = old.get(sid)
        if prev and prev.get("fingerprint") == fp and prev["verified"]:
            return dict(prev, label=ds.get(sid, {}).get("time_complexity_inferred"))
        text = p.read_text(encoding="utf-8")
        r = subprocess.run([DAFNY, "verify", str(p)],
                           capture_output=True, text=True, timeout=600)
        out = (r.stdout + r.stderr)
        ok = r.returncode == 0 and "0 errors" in out
        assumes = len(re.findall(r"\bassume\b", text))
        row = {
            "solution_id": sid,
            "label": ds.get(sid, {}).get("time_complexity_inferred"),
            "proved_bound": bound_of(text),
            "verified": ok,
            "assume_count": assumes,
            # Only Solve's `requires` can narrow the inputs; a helper's is
            # proved at every call.
            "same_python": audit.identity(str(ROOT), sid, {}, str(p)),
            "requires_changed": [m for m in audit.contract_changes(
                str(ROOT), sid, {}, str(p)) if m == "Solve"],
            "dafny_version": DAFNY_VERSION,
            "z3_version": Z3,
            "verifier_output": out.strip().splitlines()[-1] if out.strip() else "",
            "fingerprint": fp,
        }
        log(f"  {sid:>10}  {'VERIFIED' if ok else 'FAILED  '}  "
            f"label={row['label']}  bound={row['proved_bound']}"
            + ("  ASSUMES!" if assumes else ""))
        return row
    with ThreadPoolExecutor(max_workers=workers) as ex:
        rows = list(ex.map(check, files))
    files, rows = [f for f, r in zip(files, rows) if r], [r for r in rows if r]
    # Parallel load can push a proof past Z3's time limit. Re-check each failure
    # alone; only that verdict is recorded.
    for i, r in enumerate(rows):
        if not r["verified"]:
            log(f"  {r['solution_id']:>10}  failed under load; re-checking alone")
            rows[i] = check(files[i])
    write_jsonl(DATA / "complexity_proofs.jsonl", rows, key="solution_id")
    n_ok = sum(r["verified"] for r in rows)
    n_assume = sum(1 for r in rows if r["assume_count"])
    n_changed = sum(1 for r in rows if changes_row(r))
    log(f"proofs: {n_ok}/{len(rows)} verify; {n_assume} contain `assume`; "
        f"{n_changed} change their row")
    return rows


if __name__ == "__main__":
    rows = run()
    hits = scan_assumes()
    # `dafny verify` on a proof does not verify what it includes, so the
    # prelude's lemmas are checked here or nowhere.
    pre = subprocess.run([DAFNY, "verify", str(PRELUDE)],
                         capture_output=True, text=True, timeout=1200)
    pre_ok = pre.returncode == 0
    log(f"prelude: {(pre.stdout + pre.stderr).strip().splitlines()[-1]}")
    sys.exit(0 if (all(r["verified"] and not r["assume_count"] and not changes_row(r)
                       for r in rows)
                   and not hits and pre_ok) else 1)
