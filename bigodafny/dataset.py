"""Join tasks + signatures + baseline + validation into the exported dataset.

The `split` is assigned here, from the measured Python baseline rather than
from anything read out of the problem statement:

  strict       -- the original Python reproduces every stored output
                  byte-for-byte, so a Dafny translation can be held to the same
                  standard.
  loose        -- it does not. The stored output is one accepted answer among
                  several, or the solution errors or times out on its own tests.
  unvalidatable -- BigOBench's own `Input.from_str` raises on at least one of
                  the row's stored tests, so the harness cannot feed the Dafny
                  method at all. No translation of these rows can ever pass, and
                  a `fail` against them measures the parser, not the code.

Only `strict` is scored by byte-diff.
"""
from __future__ import annotations
from collections import Counter

from common import (DAFNY_VERSION, DATA, INEXACT, VERIFIED, event, log,
                    read_jsonl, write_json, write_jsonl)

EXPORT = ("problem_id", "solution_id", "problem_name", "split", "nondet_hint",
          "time_complexity_inferred", "time_curve_coefficient", "n_tests",
          "python_status", "python_pass_rate", "dafny_signature",
          "dafny_status", "dafny_tests_passed", "dafny_tests_total")


def parser_ok(task, sig=None):
    """Can the harness feed this row at all? Two ways it cannot.

    1. `from_str` raises. Four rows: their parser asserts a trailing newline the
       stored input does not have.
    2. `from_str` silently loses information. Two rows declare a `real`
       argument and carry ~100-significant-digit decimals; Python `float()`
       truncates them before Dafny is ever called, e.g.
       4.6329496401734172195e50 -> 4.632949640173417e50. No implementation can
       pass, so a `fail` there measures the harness, not the code.

    Both measured, not assumed."""
    ns = {}
    try:
        exec(compile(task["dataclass_code"], "<dc>", "exec"), ns)
        f = ns["Input"].from_str
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
            # Only checked where it can bite: a real-valued argument whose
            # decimal text does not survive the float round-trip.
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
    vpath = DATA / "validation.jsonl"
    val = ({v["solution_id"]: v for v in read_jsonl(vpath)}
           if vpath.exists() else {})

    rows = []
    for t in tasks:
        b = base.get(t["solution_id"], {})
        s = sigs.get(t["problem_id"], {})
        v = val.get(t["solution_id"], {})
        st = b.get("python_status", "unmeasured")
        n = b.get("n_tests") or 0
        pok = parser_ok(t, s)
        rows.append({
            "problem_id": t["problem_id"],
            "solution_id": t["solution_id"],
            "problem_name": t["problem_name"],
            "split": ("unvalidatable" if not pok
                      else "strict" if st == "exact" else "loose"),
            "parser_ok": pok,
            "nondet_hint": t["nondet_hint"],
            "time_complexity_inferred": t["time_complexity_inferred"],
            "time_curve_coefficient": t["time_curve_coefficient"],
            "n_tests": t["n_tests"],
            "python_status": st,
            "python_pass_rate": round(b.get("passed", 0) / n, 4) if n else None,
            "dafny_signature": s.get("dafny"),
            "signature_status": s.get("status", "missing"),
            "dafny_status": v.get("status", "untranslated"),
            # Behaviour is validated; the complexity label is not trusted.
            "quarantined": t["solution_id"] in quarantine,
            "quarantine_reasons": quarantine.get(t["solution_id"], []),
            "complexity_proved": (VERIFIED / t["problem_id"] /
                                  f'{t["solution_id"]}.dfy').exists(),
            "dafny_tests_passed": v.get("tests_passed"),
            "dafny_tests_total": v.get("tests_total"),
        })
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
        "time_complexity": dict(Counter(r["time_complexity_inferred"]
                                        for r in rows).most_common()),
        "strict_by_complexity": dict(Counter(
            r["time_complexity_inferred"] for r in rows
            if r["split"] == "strict").most_common()),
    }
    write_json(DATA / "stats.json", stats)
    event("dataset", **{k: stats[k] for k in ("rows", "problems", "splits")})
    log(f"dataset: {len(rows)} rows over {stats['problems']} problems")
    log(f"  splits: {dict(split)}")
    log(f"  dafny:  {stats['dafny_status']}")
    return rows


if __name__ == "__main__":
    build()
