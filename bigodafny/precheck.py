"""Check every `requires` added to a translation against every stored input.

Adding a precondition is the cheap way to make `dafny verify` pass: narrow the
contract until the obligation is trivial. That is only honest if the precondition
is something the problem actually guarantees. If it fails on inputs the harness
really feeds, the proof covers a domain the data does not visit.

This translates the common Dafny precondition shapes into Python and evaluates
them against the parsed test inputs. Shapes it cannot translate are reported as
`unchecked` -- they need reading, not guessing.
"""
from __future__ import annotations
import json, re, sys
from pathlib import Path

from common import DATA, INEXACT, SOLUTIONS, UNVERIFIED, log, read_jsonl, write_jsonl

ROOTS = [SOLUTIONS, UNVERIFIED, INEXACT]


def find(sid, pid):
    for r in ROOTS:
        p = r / pid / f"{sid}.dfy"
        if p.exists():
            return p
    return None


def requires_of(text):
    head = text.split("method Solve(", 1)[1].split("{", 1)[0] if "method Solve(" in text else ""
    out, cur = [], None
    for line in head.splitlines():
        s = line.strip()
        if s.startswith("requires "):
            if cur:
                out.append(cur)
            cur = s[len("requires "):]
        elif cur is not None and s and not s.startswith(("ensures", "decreases", "modifies")):
            cur += " " + s
        elif cur:
            out.append(cur); cur = None
    if cur:
        out.append(cur)
    return [re.sub(r"\s+", " ", c).strip() for c in out]


def to_python(clause, bound=()):
    """Translate one Dafny precondition into a Python expression over `I`."""
    s = clause
    # Guard first, on the ORIGINAL text: a call to a Dafny function we cannot
    # evaluate. Doing this after the |x| -> len(...) rewrite would match our own
    # generated `len(`.
    if re.search(r"(?<![|\w])[A-Za-z_]\w*\s*\(", s):
        return None
    m = re.match(r"forall (\w+) :: 0 <= \1 < (\|\w+\||\w+) ==> (.+)$", s)
    if m:
        var, hi, body = m.groups()
        inner = to_python(body, tuple(bound) + (var,))
        if inner is None:
            return None
        hi_py = (f"len(I.{hi[1:-1]})" if hi.startswith("|") else f"I.{hi}")
        return f"all(({inner}) for {var} in range({hi_py}))"
    s = re.sub(r"\|(\w+)\[(\w+)\]\|", r"len(\1[\2])", s)
    s = re.sub(r"\|(\w+)\|", r"len(\1)", s)
    s = re.sub(r"(\w+)\[(\w+)\]\.(\d)", r"\1[\2][\3]", s)

    s = s.replace("&&", " and ").replace("||", " or ")
    # bare identifiers that are not python keywords/numbers -> Input fields
    def field(mo):
        w = mo.group(0)
        if w in ("and", "or", "not", "len", "all", "range", "I", "true",
                 "false") or w in bound:
            return w
        return f"I.{w}"
    s = re.sub(r"(?<![.\w])[a-zA-Z_]\w*(?![\w(])", field, s)
    return s


def run(sids):
    tasks = {t["solution_id"]: t for t in read_jsonl(DATA / "tasks.jsonl")}
    rows = []
    for sid in sids:
        pid = sid.split("_")[0]
        p = find(sid, pid)
        if p is None or sid not in tasks:
            continue
        clauses = requires_of(p.read_text(encoding="utf-8"))
        if not clauses:
            continue
        t = tasks[sid]
        ns = {}
        exec(compile(t["dataclass_code"], "<dc>", "exec"), ns)
        for c in clauses:
            expr = to_python(c)
            rec = {"solution_id": sid, "clause": c, "expr": expr,
                   "holds": 0, "violated": 0, "error": 0}
            if expr is None:
                rec["status"] = "unchecked"
                rows.append(rec); continue
            for k in ("public_tests", "private_tests", "generated_tests"):
                for tst in t["tests"].get(k, []):
                    try:
                        I = ns["Input"].from_str(tst["input"])
                        val = eval(expr, {"len": len, "all": all,
                                          "range": range, "I": I})
                        rec["holds" if val else "violated"] += 1
                    except Exception:
                        rec["error"] += 1
            rec["status"] = ("violated" if rec["violated"] else
                             "ok" if rec["holds"] else "no-data")
            rows.append(rec)
    write_jsonl(DATA / "precondition_check.jsonl", rows)
    bad = [r for r in rows if r["status"] == "violated"]
    unk = [r for r in rows if r["status"] == "unchecked"]
    log(f"preconditions: {len(rows)} clauses over {len({r['solution_id'] for r in rows})} rows")
    log(f"  ok        {sum(1 for r in rows if r['status']=='ok')}")
    log(f"  VIOLATED  {len(bad)}")
    log(f"  unchecked {len(unk)}  (needs reading, not guessing)")
    for r in bad:
        log(f"    VIOLATED {r['solution_id']}: {r['clause']}  "
            f"(holds {r['holds']}, violated {r['violated']})")
    for r in unk:
        log(f"    unchecked {r['solution_id']}: {r['clause']}")
    return rows


if __name__ == "__main__":
    ids = sys.argv[1:]
    if not ids:
        print("usage: precheck.py SID..."); sys.exit(2)
    run(ids)
