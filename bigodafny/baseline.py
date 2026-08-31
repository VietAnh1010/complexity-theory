"""Run each original Python solution against its own stored tests.

This is the ceiling for any translation. A Dafny row cannot be expected to
match byte-for-byte what the Python it was translated from does not match:
Codeforces accepted many of these under a token-based or special checker, so
the stored `output` is one accepted answer, not the only one.

The result defines the `strict` split by measurement instead of by reading the
problem statement for phrases like "print any of them".
"""
from __future__ import annotations
import json, subprocess, sys, tempfile
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

from common import DATA, event, log, read_jsonl, write_jsonl

RUNNER = r'''
import json, signal, sys, io, os
sys.setrecursionlimit(100000)
code = open(sys.argv[1], encoding="utf-8").read()
tests = json.load(open(sys.argv[2], encoding="utf-8"))
class T(Exception): pass
def _a(s, f): raise T()
signal.signal(signal.SIGALRM, _a)
res = []
obj = compile(code, "sol", "exec")
for t in tests:
    signal.alarm(10)
    so, si = sys.stdout, sys.stdin
    buf = io.StringIO()
    try:
        sys.stdin = io.StringIO(t["input"]); sys.stdout = buf
        exec(obj, {"__name__": "__main__"})
        sys.stdout, sys.stdin = so, si
        res.append("pass" if buf.getvalue().rstrip() == t["output"].rstrip() else "fail")
    except T:
        sys.stdout, sys.stdin = so, si; res.append("timeout")
    except SystemExit:
        sys.stdout, sys.stdin = so, si
        res.append("pass" if buf.getvalue().rstrip() == t["output"].rstrip() else "fail")
    except Exception:
        sys.stdout, sys.stdin = so, si; res.append("error")
    finally:
        signal.alarm(0)
json.dump(res, sys.stdout)
'''


def one(task):
    tests = [{"input": t["input"], "output": t["output"]}
             for k in ("public_tests", "private_tests")
             for t in task["tests"].get(k, [])]
    rec = {"solution_id": task["solution_id"], "problem_id": task["problem_id"],
           "n_tests": len(tests)}
    if not tests:
        return {**rec, "python_status": "no-tests", "passed": 0}
    with tempfile.TemporaryDirectory() as d:
        d = Path(d)
        (d / "r.py").write_text(RUNNER, encoding="utf-8")
        (d / "s.py").write_text(task["solution_code"], encoding="utf-8")
        (d / "t.json").write_text(json.dumps(tests), encoding="utf-8")
        try:
            p = subprocess.run([sys.executable, str(d / "r.py"), str(d / "s.py"),
                                str(d / "t.json")],
                               capture_output=True, text=True, timeout=400, cwd=d)
            res = json.loads(p.stdout)
        except Exception as e:
            return {**rec, "python_status": "harness-error",
                    "passed": 0, "error": f"{type(e).__name__}"[:80]}
    c = Counter(res)
    return {**rec, "passed": c["pass"], "failed": c["fail"],
            "timeout": c["timeout"], "errored": c["error"],
            "python_status": "exact" if c["pass"] == len(res)
            else ("none" if c["pass"] == 0 else "partial")}


def run(workers=8):
    tasks = list(read_jsonl(DATA / "tasks.jsonl"))
    log(f"running {len(tasks)} original Python solutions against their own tests")
    with ProcessPoolExecutor(max_workers=workers) as ex:
        rows = list(ex.map(one, tasks, chunksize=4))
    rows.sort(key=lambda r: (int(r["problem_id"]), r["solution_id"]))
    write_jsonl(DATA / "baseline.jsonl", rows)
    st = Counter(r["python_status"] for r in rows)
    log(f"python baseline: {dict(st)}")
    event("baseline", **st)
    return rows


if __name__ == "__main__":
    run()
