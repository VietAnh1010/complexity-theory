"""Check every `requires` of a row against every stored input.

Adding a precondition is the cheap way to make `dafny verify` pass: narrow the
contract until the obligation is trivial. That is only honest if the precondition
is something the problem actually guarantees. If it fails on inputs the harness
really feeds, the proof covers a domain the data does not visit.

Dafny evaluates the clauses itself. Each copy of the row gains one compiled
method per clause, `PreCheck<i>(<Solve's parameters>)`, whose body is that
clause; `dafny translate py` builds it and the methods run on every parsed
input. Any clause Dafny can compile is checked with Dafny's own semantics, so
no clause shape needs a translation written for it. A clause Dafny cannot
compile (an unbounded quantifier, a ghost helper calling another ghost) is
reported `unchecked` with the compiler's message.
"""
from __future__ import annotations
import argparse, json, re, subprocess, sys
from concurrent.futures import ProcessPoolExecutor

from common import (WORKERS, BUILD, DATA, UNSCREENED, SOLUTIONS, UNVERIFIED,
                    PROVED, PRELUDE, log, read_jsonl, write_jsonl, DISPUTED,
                    UNGATEABLE, PROVED_VALUE, UNSURE, in_spec)
from validate import build_one, conv_expr

# solutions-proved/ was missing here, so the twelve
# complexity proofs' preconditions were never checked against real inputs --
# and the proofs are exactly where new preconditions get added, to make a
# bound provable. Two of the twelve turned out to exclude inputs their own
# row answers. A gate that skips the files most likely to need it is not a
# gate.
ROOTS = [SOLUTIONS, UNVERIFIED, UNSCREENED, PROVED, PROVED_VALUE,
         DISPUTED, UNGATEABLE, UNSURE]


def find_all(sid, pid):
    """EVERY copy of the row, not the first.

    A row can exist in two places at once: the plain translation in
    `solutions/` or `solutions-unscreened/`, and an instrumented copy carrying a
    complexity proof in `solutions-proved/`.
    Returning
    only the first meant the proofs -- the copies most likely to have gained a
    new `requires`, since that is often what makes a bound provable -- were
    never the file this checked. 827_148 has two different precondition sets in
    two directories and only the weaker one was ever seen.
    """
    return [r / pid / f"{sid}.dfy" for r in ROOTS
            if (r / pid / f"{sid}.dfy").exists()]


SOLVE = re.compile(r"\bmethod\s+(?:\{[^}]*\}\s*)*Solve\(")


def solve_header(text):
    """(parameter list, text between `)` and the body's `{`) of Solve.

    The pattern allows attributes: `method {:isolate_assertions} Solve(` did
    not match a plain `method Solve(` search, so such proofs went unchecked."""
    m = SOLVE.search(text)
    if not m:
        return None, ""
    depth, i = 1, m.end()
    while depth:
        depth += {"(": 1, ")": -1}.get(text[i], 0)
        i += 1
    return text[m.end():i - 1], text[i:text.index("\n{", i)]


def requires_of(head):
    out, cur = [], None
    for line in head.splitlines():
        s = line.split("//", 1)[0].strip()   # a comment is never part of a clause
        if not s:
            continue
        if s.startswith("requires "):
            if cur:
                out.append(cur)
            cur = s[len("requires "):]
        elif cur is not None and not s.startswith(("ensures", "decreases",
                                                    "modifies", "returns")):
            cur += " " + s
        elif cur:
            out.append(cur); cur = None
    if cur:
        out.append(cur)
    return [re.sub(r"\s+", " ", c).strip() for c in out]


def unghost(text, names):
    """Compile the ghost functions a clause calls. A ghost function is pure,
    so compiling it changes speed, not values. Only those: some prelude ghosts
    have unbounded quantifiers and cannot compile."""
    for n in names:
        text = re.sub(rf"\bghost (function|predicate) {n}\b", rf"\1 {n}", text)
    return text


HARNESS = '''\
import json, signal, sys
from fractions import Fraction
sys.path.insert(0, {pydir!r})
sys.setrecursionlimit(100000)
import _dafny
import module_


def _mkreal(x):
    f = Fraction(x).limit_denominator(10 ** 12)
    return _dafny.BigRational(f.numerator, f.denominator)


_ns = {{}}
exec(compile(open({dcpath!r}, encoding="utf-8").read(), "dataclass", "exec"), _ns)
Input = _ns["Input"]


class _Timeout(Exception):
    pass


def _alarm(signum, frame):
    raise _Timeout()


signal.signal(signal.SIGALRM, _alarm)
out = []
for raw in json.load(open({testspath!r}, encoding="utf-8")):
    try:
        inp = Input.from_str(raw)
    except Exception:
        out.append(None)
        continue
    row = []
    for i in range({n}):
        signal.alarm(30)
        try:
            row.append(bool(getattr(module_.default__, "PreCheck%d" % i)({args})))
        except BaseException:
            row.append(None)
        finally:
            signal.alarm(0)
    out.append(row)
json.dump(out, sys.stdout)
'''


def python_fails(code, stdin, timeout=20):
    """Does the row's ORIGINAL Python fail on this input?"""
    try:
        p = subprocess.run([sys.executable, "-c", code], input=stdin,
                           capture_output=True, text=True, timeout=timeout)
        return p.returncode != 0
    except Exception:
        return True


def check_file(job):
    """Every clause of one copy of one row: one record per clause."""
    t, sig, p = job
    sid, root = t["solution_id"], p.parent.parent.name
    text = p.read_text(encoding="utf-8")
    params, head = solve_header(text)
    clauses = requires_of(head) if params is not None else []
    if not clauses:
        return []
    recs = [{"solution_id": sid, "root": root, "clause": c,
             "holds": 0, "violated": 0, "error": 0, "out_of_spec": 0}
            for c in clauses]

    work = BUILD / f"precheck_{root}_{sid}"
    work.mkdir(parents=True, exist_ok=True)
    names = set(re.findall(r"\b([A-Za-z_]\w*)\(", " ".join(clauses)))
    (work / "prelude.dfy").write_text(
        unghost(PRELUDE.read_text(encoding="utf-8"), names), encoding="utf-8")
    body = re.sub(r'include "[^"]*prelude\.dfy"', 'include "prelude.dfy"',
                  unghost(text, names))
    body += "".join(f"\n\nmethod PreCheck{i}({params}) returns (ok: bool)\n"
                    f"{{\n  ok := {c};\n}}\n" for i, c in enumerate(clauses))
    (work / "row.dfy").write_text(body, encoding="utf-8")
    pydir, err = build_one(work / "row.dfy", work)
    if err:
        return [{**r, "status": "unchecked", "error_text": err[:300]} for r in recs]

    tests = [(k, x["input"]) for k in ("public_tests", "private_tests",
                                       "generated_tests")
             for x in t["tests"].get(k, [])]
    kept = []
    for k, inp in tests:
        if in_spec(t, inp):
            kept.append((k, inp))
        else:
            for r in recs:
                r["out_of_spec"] += 1
    (work / "dataclass.py").write_text(t["dataclass_code"], encoding="utf-8")
    (work / "tests.json").write_text(json.dumps([inp for _, inp in kept]),
                                     encoding="utf-8")
    args = ", ".join(conv_expr(q["dafny_type"], f'inp.{q["py_name"]}')
                     for q in sig["params"])
    (work / "harness.py").write_text(HARNESS.format(
        pydir=str(pydir), dcpath=str(work / "dataclass.py"),
        testspath=str(work / "tests.json"), n=len(clauses), args=args),
        encoding="utf-8")
    try:
        r = subprocess.run([sys.executable, str(work / "harness.py")],
                           capture_output=True, text=True,
                           timeout=60 + 30 * len(kept) * len(clauses))
        res = json.loads(r.stdout)
    except Exception as e:
        return [{**x, "status": "unchecked",
                 "error_text": f"harness: {type(e).__name__}"} for x in recs]

    for i, rec in enumerate(recs):
        offenders, by_tier = [], {}
        for (k, inp), row in zip(kept, res):
            val = None if row is None else row[i]
            if val is None:
                rec["error"] += 1
            elif val:
                rec["holds"] += 1
            else:
                rec["violated"] += 1
                by_tier[k] = by_tier.get(k, 0) + 1
                offenders.append(inp)
        if rec["violated"]:
            # A precondition may exclude an input the ORIGINAL Python also
            # fails on: the row's contract is to reproduce that Python, and
            # there is no behaviour to reproduce. Excluding an input the
            # Python handles is the dishonest case.
            live = sum(1 for inp in offenders
                       if not python_fails(t["solution_code"], inp))
            rec["violated_python_ok"] = live
            rec["violated_by_tier"] = by_tier
            real = by_tier.get("public_tests", 0) + by_tier.get("private_tests", 0)
            if not live:
                rec["status"] = "violated-python-also-fails"
            elif not real:
                # Only BigOBench's synthetic `generated_tests` violate it.
                # Those are scaled inputs and can leave the problem's own
                # stated constraints -- 827_148's cap is the statement's
                # own `1 <= si, di <= 1000`, honoured by all 35 real tests
                # and exceeded (max 1101) by 39 generated ones. A clause
                # faithful to the statement is not the same defect as one
                # that excludes a real test, and collapsing them would
                # either excuse the second or condemn the first.
                rec["status"] = "violated-generated-only"
            else:
                rec["status"] = "violated"
        else:
            rec["status"] = "ok" if rec["holds"] else "no-data"
    return recs


def all_sids():
    """Every row with a copy whose Solve carries a `requires`, and every row
    the record names: a copy that lost its clauses or its file (1972_295's
    proof) must have its old lines dropped, not kept."""
    rec = DATA / "precondition_check.jsonl"
    out = {r["solution_id"] for r in read_jsonl(rec)} if rec.exists() else set()
    for r in ROOTS:
        for p in r.rglob("*.dfy"):
            params, head = solve_header(p.read_text(encoding="utf-8"))
            if params is not None and requires_of(head):
                out.add(p.stem)
    return sorted(out)


def run(sids, workers=WORKERS):
    tasks = {t["solution_id"]: t for t in read_jsonl(DATA / "tasks.jsonl")}
    sigs = {s["problem_id"]: s for s in read_jsonl(DATA / "signatures.jsonl")}
    checked = {sid for sid in sids if sid in tasks}
    jobs = [(tasks[sid], sigs[tasks[sid]["problem_id"]], p)
            for sid in sorted(checked)
            for p in find_all(sid, tasks[sid]["problem_id"])]
    log(f"checking the requires of {len(jobs)} file(s) over {len(checked)} row(s)")
    with ProcessPoolExecutor(max_workers=workers) as ex:
        rows = [rec for recs in ex.map(check_file, jobs) for rec in recs]
    # This tool runs on the rows it is given, so the file must accumulate.
    # Replacing it meant the record held whichever row was checked last: four
    # clauses of one row, for a corpus with preconditions in dozens. A re-check
    # of a row replaces ALL that row's clauses and leaves every other row alone
    # -- including when the re-check finds none: a copy that lost its last
    # `requires`, or moved, must not keep its old clauses (1077_84 did, until
    # the main agent removed them).
    out = DATA / "precondition_check.jsonl"
    prior = [r for r in read_jsonl(out)] if out.exists() else []
    merged = [r for r in prior if r.get("solution_id") not in checked] + rows
    merged.sort(key=lambda r: (r.get("solution_id", ""), r.get("root", ""),
                               r.get("clause", "")))
    write_jsonl(out, merged, key=("solution_id", "root", "clause"))
    log(f"precondition_check.jsonl now holds {len(merged)} clause(s) over "
        f"{len({r.get('solution_id') for r in merged})} row(s)")
    bad = [r for r in rows if r["status"] == "violated"]
    unk = [r for r in rows if r["status"] == "unchecked"]
    nod = [r for r in rows if r["status"] == "no-data"]
    vpf = [r for r in rows if r["status"] == "violated-python-also-fails"]
    vgo = [r for r in rows if r["status"] == "violated-generated-only"]
    log(f"preconditions: {len(rows)} clauses over {len({r['solution_id'] for r in rows})} rows")
    log(f"  ok        {sum(1 for r in rows if r['status']=='ok')}")
    log(f"  VIOLATED  {len(bad)}")
    log(f"  unchecked {len(unk)}  (Dafny could not compile the clause)")
    log(f"  no-data   {len(nod)}  (compiled but never evaluated -- NOT a pass)")
    log(f"  py-fails  {len(vpf)}  (violated only where the original Python also fails)")
    log(f"  gen-only  {len(vgo)}  (violated only by synthetic generated_tests, "
        f"never by a real one)")
    for r in bad:
        log(f"    VIOLATED {r['solution_id']} ({r['root']}): {r['clause']}  "
            f"(holds {r['holds']}, violated {r['violated']}, of which "
            f"{r.get('violated_python_ok', '?')} run fine in Python)")
    for r in unk:
        log(f"    unchecked {r['solution_id']} ({r['root']}): {r['clause']}  "
            f"[{r.get('error_text', '').splitlines()[0][:120] if r.get('error_text') else ''}]")
    for r in nod:
        log(f"    no-data {r['solution_id']} ({r['root']}): {r['clause']}  "
            f"(errors {r['error']})")
    for r in vgo:
        log(f"    gen-only {r['solution_id']}: {r['clause']}  "
            f"(holds {r['holds']}, violated {r['violated']}, all in "
            f"generated_tests)")
    for r in vpf:
        log(f"    py-fails {r['solution_id']}: {r['clause']}  "
            f"(holds {r['holds']}, violated {r['violated']}, all of which "
            f"crash the original Python)")
    return rows


if __name__ == "__main__":
    ap = argparse.ArgumentParser(prog="precheck.py")
    ap.add_argument("sids", nargs="*")
    ap.add_argument("--all", action="store_true",
                    help="every row whose Solve has a requires")
    ap.add_argument("--workers", type=int, default=WORKERS)
    a = ap.parse_args()
    ids = all_sids() if a.all else a.sids
    if not ids:
        ap.error("give SIDs or --all")
    run(ids, workers=a.workers)
