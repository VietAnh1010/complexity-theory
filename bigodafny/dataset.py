"""Join tasks + signatures + baseline + validation into the exported dataset.

The `split`, from the measured Python baseline:

  strict        -- the original Python reproduces every stored output byte for
                   byte; only these rows are scored by byte-diff.
  loose         -- it does not, or it errors or times out on its own tests.
  unvalidatable -- the harness cannot feed the Dafny the stored tests.
"""
from __future__ import annotations
from collections import Counter

from common import (DAFNY_VERSION, DATA, UNTRANSLATED, PROVED,
                    log, read_jsonl, write_json, write_jsonl)


def parser_ok(task, sig=None):
    """Can the harness feed this row? Not when `from_str` raises, or when it
    loses a `real` argument's digits to `float()`."""
    ns = {}
    try:
        exec(compile(task["dataclass_code"], "<dc>", "exec"), ns)
        f = ns["Input"].from_str
    except ImportError:
        raise  # no numpy: outside .venv. Not a row fact; must not become one.
    except Exception:
        return False
    has_real = bool(sig and sig.get("status") == "ok"
                    and any(p["dafny_type"] == "real" for p in sig["params"]))
    for k in ("public_tests", "private_tests"):
        for t in task["tests"].get(k, []):
            try:
                parsed = f(t["input"])
            except Exception:
                return False
            if has_real and repr(parsed) != t["input"]:
                return False
    return True


def build():
    tasks = list(read_jsonl(DATA / "tasks.jsonl"))
    sigs = {s["problem_id"]: s for s in read_jsonl(DATA / "signatures.jsonl")}
    base = {b["solution_id"]: b for b in read_jsonl(DATA / "baseline.jsonl")}
    qpath = DATA / "quarantine.jsonl"
    quarantine = ({q["solution_id"]: q["reasons"] for q in read_jsonl(qpath)}
                  if qpath.exists() else {})
    fpath = DATA / "verification.jsonl"
    verif = ({f["solution_id"]: f for f in read_jsonl(fpath)}
             if fpath.exists() else {})
    vpath = DATA / "validation.jsonl"
    val = ({v["solution_id"]: v for v in read_jsonl(vpath)}
           if vpath.exists() else {})
    # `difftest.py` is the gate for loose rows; `validate.py` never runs on them.
    dpath = DATA / "difftest.jsonl"
    diff = ({d["solution_id"]: d for d in read_jsonl(dpath)}
            if dpath.exists() else {})
    # A label a proof showed wrong. `time_complexity_inferred` stays
    # BigOBench's; `label` is the one the corpus uses.
    cpath = DATA / "label_corrections.jsonl"
    corrected = ({c["solution_id"]: c["label"] for c in read_jsonl(cpath)}
                 if cpath.exists() else {})
    # Inputs to `blockers`: the label verdict, the proof, the ungateable
    # record, and precheck clauses on the row itself (not on a proof copy).
    audit = {a["sid"]: a for a in read_jsonl(DATA / "label_audit.jsonl")}
    proofs = {p["solution_id"]: p
              for p in read_jsonl(DATA / "complexity_proofs.jsonl")}
    ungateable = {g["solution_id"]
                  for g in read_jsonl(DATA / "gate_ungateable.jsonl")}
    bad_clause = {c["solution_id"]
                  for c in read_jsonl(DATA / "precondition_check.jsonl")
                  if c["root"] not in ("solutions-proved", "value-bounded")
                  and c["status"] not in ("ok", "violated-python-also-fails")}

    rows = []
    for t in tasks:
        b = base.get(t["solution_id"], {})
        s = sigs.get(t["problem_id"], {})
        v = val.get(t["solution_id"], {})
        dt = diff.get(t["solution_id"], {})
        st = b.get("python_status", "unmeasured")
        n = b.get("n_tests") or 0
        pok = parser_ok(t, s)
        row_split = ("unvalidatable" if not pok
                     else "strict" if st == "exact" else "loose")
        gate_name = "validate" if row_split == "strict" else "difftest"
        gate_rec = v if row_split == "strict" else dt
        rows.append({
            "problem_id": t["problem_id"],
            "solution_id": t["solution_id"],
            "problem_name": t["problem_name"],
            "split": row_split,
            "parser_ok": pok,
            "nondet_hint": t["nondet_hint"],
            "time_complexity_inferred": t["time_complexity_inferred"],
            "label": corrected.get(t["solution_id"], t["time_complexity_inferred"]),
            "label_corrected": t["solution_id"] in corrected,
            "time_curve_coefficient": t["time_curve_coefficient"],
            "n_tests": t["n_tests"],
            "python_status": st,
            "python_pass_rate": round(b.get("passed", 0) / n, 4) if n else None,
            "dafny_signature": s.get("dafny"),
            "signature_status": s.get("status", "missing"),
            # Each split reports its own gate's status, never another gate's
            # stale record. `agrees` is a loose row's pass.
            "dafny_status": (gate_rec.get("status") or "untranslated"),
            "dafny_gate": (gate_name if gate_rec.get("status") else None),
            # Behaviour is validated; the complexity label is not trusted.
            "quarantined": t["solution_id"] in quarantine,
            "quarantine_reasons": quarantine.get(t["solution_id"], []),
            # Deliberately not translated; the file states why.
            "untranslatable": (UNTRANSLATED / t["problem_id"] /
                               f'{t["solution_id"]}.dfy').exists(),
            "complexity_proved": any(
                PROVED.rglob(f'{t["solution_id"]}.dfy')),
            # `dafny verify` with no user spec: seq bounds, division, termination.
            "safety_verified": verif.get(t["solution_id"], {}).get("verified"),
            "safety_failure": verif.get(t["solution_id"], {}).get("kind"),
            "dafny_tests_passed": gate_rec.get("tests_passed",
                                               gate_rec.get("agree")),
            "dafny_tests_total": gate_rec.get("tests_total",
                                              gate_rec.get("comparable")),
        })
        # What keeps the row from being clean (STATUS.md § Clean rows).
        r, sid, pf = rows[-1], t["solution_id"], proofs.get(t["solution_id"])
        vf = verif.get(sid, {})
        r["blockers"] = ["untranslatable"] if r["untranslatable"] else [
            name for name, hit in [
                ("tests", r["dafny_status"] not in ("valid", "agrees")
                 and sid not in ungateable),
                ("unverified", not vf.get("verified")),
                ("decreases-star", vf.get("termination_opt_out")),
                ("precheck", sid in bad_clause),
                ("truth-unsettled", audit.get(sid, {}).get("verdict") != "ok"),
                ("no-proof", pf is None),
                ("proof-fails", pf is not None and not (
                    pf["verified"] and pf["assume_count"] == 0)),
                ("proof-changes-row", pf is not None and (
                    pf.get("same_python") != "identical"
                    or bool(pf.get("requires_changed")))),
            ] if hit]
        r["clean"] = not r["blockers"]
    rows.sort(key=lambda r: (int(r["problem_id"]), r["solution_id"]))
    write_jsonl(DATA / "dataset.jsonl", rows)

    split = Counter(r["split"] for r in rows)
    stats = {
        "dafny_version": DAFNY_VERSION,
        "rows": len(rows),
        "problems": len({r["problem_id"] for r in rows}),
        "splits": dict(split),
        "problems_per_split": {s: len({r["problem_id"] for r in rows
                                       if r["split"] == s}) for s in split},
        "python_status": dict(Counter(r["python_status"] for r in rows)),
        "signature_status": dict(Counter(r["signature_status"] for r in rows)),
        "dafny_status": dict(Counter(r["dafny_status"] for r in rows)),
        "quarantined": sum(r["quarantined"] for r in rows),
        "quarantine_reasons": dict(Counter(
            x for r in rows for x in r["quarantine_reasons"])),
        "complexity_proved": sum(r["complexity_proved"] for r in rows),
        "labels_corrected": sum(r["label_corrected"] for r in rows),
        "untranslatable": sum(r["untranslatable"] for r in rows),
        "safety_verified": sum(1 for r in rows if r["safety_verified"]),
        "safety_failure": dict(Counter(r["safety_failure"] for r in rows
                                       if r["safety_failure"])),
        "clean": sum(r["clean"] for r in rows),
        "blockers": dict(Counter(
            x for r in rows for x in r["blockers"]).most_common()),
        "time_complexity": dict(Counter(r["time_complexity_inferred"]
                                        for r in rows).most_common()),
        "strict_by_complexity": dict(Counter(
            r["time_complexity_inferred"] for r in rows
            if r["split"] == "strict").most_common()),
    }
    write_json(DATA / "stats.json", stats)
    log(f"dataset: {len(rows)} rows over {stats['problems']} problems")
    log(f"  splits: {dict(split)}")
    log(f"  dafny:  {stats['dafny_status']}")
    return rows


if __name__ == "__main__":
    build()
