"""Differential test: does the Dafny print what the PYTHON prints?

`validate.py` compares against BigOBench's stored output. That works only for
the 534 `strict` rows. For the 100 `loose` rows the stored output is one
accepted answer among several -- Codeforces judged them with a token-based or
special checker -- so even the original Python fails a byte-diff against it.

Those rows are still translatable, and there is still an exact question to ask:
does the translation reproduce *its own Python*, input for input? That is the
right equivalence for a transpilation dataset, and it is decidable even when the
stored output is not.

Where both gates apply they should agree; `strict` rows can be run under either.
"""
from __future__ import annotations
import argparse, json, subprocess, sys, tempfile
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

from common import DATA, event, log, read_jsonl, write_json, write_jsonl
from validate import build_one, conv_expr, HARNESS
from common import BUILD, INEXACT, SOLUTIONS, UNVERIFIED, VERIFIED

PY_RUNNER = r'''
import json, signal, sys, io
sys.setrecursionlimit(100000)
code = open(sys.argv[1], encoding="utf-8").read()
tests = json.load(open(sys.argv[2], encoding="utf-8"))
class T(Exception): pass
signal.signal(signal.SIGALRM, lambda s, f: (_ for _ in ()).throw(T()))
obj = compile(code, "sol", "exec")
out = []
for t in tests:
    signal.alarm(30)
    so, si = sys.stdout, sys.stdin
    buf = io.StringIO()
    try:
        sys.stdin = io.StringIO(t["input"]); sys.stdout = buf
        exec(obj, {"__name__": "__main__"})
        out.append({"ok": True, "out": buf.getvalue()})
    except SystemExit:
        out.append({"ok": True, "out": buf.getvalue()})
    except T:
        out.append({"ok": False, "why": "timeout"})
    except Exception as e:
        out.append({"ok": False, "why": type(e).__name__})
    finally:
        sys.stdout, sys.stdin = so, si
        signal.alarm(0)
json.dump(out, sys.stdout)
'''


def python_outputs(task, tests):
    with tempfile.TemporaryDirectory() as d:
        d = Path(d)
        (d / "r.py").write_text(PY_RUNNER, encoding="utf-8")
        (d / "s.py").write_text(task["solution_code"], encoding="utf-8")
        (d / "t.json").write_text(json.dumps(tests), encoding="utf-8")
        try:
            p = subprocess.run([sys.executable, str(d / "r.py"), str(d / "s.py"),
                                str(d / "t.json")], capture_output=True,
                               text=True, timeout=900, cwd=d)
            return json.loads(p.stdout)
        except Exception:
            return None


def find(sid, pid):
    for r in (SOLUTIONS, UNVERIFIED, INEXACT, VERIFIED):
        p = r / pid / f"{sid}.dfy"
        if p.exists():
            return p
    return None


def one(args):
    sid, tiers = args
    tasks = one.tasks
    sigs = one.sigs
    t = tasks[sid]
    dfy = find(sid, t["problem_id"])
    rec = {"solution_id": sid, "problem_id": t["problem_id"]}
    if dfy is None or "TODO: translate" in dfy.read_text(encoding="utf-8"):
        return {**rec, "status": "untranslated"}
    tests = [{"input": x["input"], "output": x["output"]}
             for k in tiers for x in t["tests"].get(k, [])]
    if not tests:
        return {**rec, "status": "no-tests"}

    py = python_outputs(t, tests)
    if py is None:
        return {**rec, "status": "python-harness-error"}

    work = BUILD / f"diff_{sid}"
    work.mkdir(parents=True, exist_ok=True)
    pydir, err = build_one(dfy, work)
    if err:
        return {**rec, "status": "build", "error": err[:300]}

    # Reuse validate's harness, but expect the PYTHON's output.
    exp = [{"input": tests[i]["input"],
            "output": py[i]["out"] if py[i]["ok"] else "\x00PYFAIL"}
           for i in range(len(tests))]
    (work / "dataclass.py").write_text(t["dataclass_code"], encoding="utf-8")
    (work / "tests.json").write_text(json.dumps(exp), encoding="utf-8")
    sig = sigs[t["problem_id"]]
    a = ", ".join(conv_expr(p["dafny_type"], f'inp.{p["py_name"]}')
                  for p in sig["params"])
    (work / "harness.py").write_text(
        HARNESS.format(pydir=str(pydir), dcpath=str(work / "dataclass.py"),
                       testspath=str(work / "tests.json"), per_test=30, args=a),
        encoding="utf-8")
    try:
        p = subprocess.run([sys.executable, str(work / "harness.py")],
                           capture_output=True, text=True, timeout=900)
        res = json.loads(p.stdout)
    except Exception as e:
        return {**rec, "status": "error", "error": f"{type(e).__name__}"}

    c = Counter()
    for i, r in enumerate(res):
        if not py[i]["ok"]:
            c["python-failed"] += 1          # nothing to compare against
        else:
            c[r["status"]] += 1
    comparable = sum(v for k, v in c.items() if k != "python-failed")
    return {**rec, "status": ("agrees" if c["pass"] == comparable and comparable
                              else "differs" if comparable else "no-comparable"),
            "agree": c["pass"], "comparable": comparable,
            "python_failed": c["python-failed"], "detail": dict(c)}


def init(tasks, sigs):
    one.tasks, one.sigs = tasks, sigs


def run(sids, tiers=("public_tests", "private_tests"), workers=6):
    tasks = {t["solution_id"]: t for t in read_jsonl(DATA / "tasks.jsonl")}
    sigs = {s["problem_id"]: s for s in read_jsonl(DATA / "signatures.jsonl")}
    log(f"differential-testing {len(sids)} rows against their own Python")
    with ProcessPoolExecutor(max_workers=workers, initializer=init,
                             initargs=(tasks, sigs)) as ex:
        rows = list(ex.map(one, [(s, tiers) for s in sids], chunksize=1))
    rows.sort(key=lambda r: (int(r["problem_id"]), r["solution_id"]))
    write_jsonl(DATA / "difftest.jsonl", rows)
    st = Counter(r["status"] for r in rows)
    write_json(DATA / "difftest_summary.json", dict(st))
    event("difftest", **st)
    log(f"result: {dict(st)}")
    return rows


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", nargs="*")
    ap.add_argument("--loose", action="store_true", help="all loose rows")
    ap.add_argument("--workers", type=int, default=6)
    a = ap.parse_args()
    if a.loose:
        ids = [r["solution_id"] for r in read_jsonl(DATA / "dataset.jsonl")
               if r["split"] == "loose"]
    else:
        ids = a.only or []
    if not ids:
        print("nothing to do"); sys.exit(2)
    run(ids, workers=a.workers)
