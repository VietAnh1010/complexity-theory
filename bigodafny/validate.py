"""Compile a .dfy to Python, drive it with BigOBench's own parser, diff stdout.

A row is valid only if it translates AND every executed test matches. The three
failure modes are recorded separately: `build` (Dafny rejected it), `fail` (it
ran and printed the wrong thing), `timeout`/`error` (it did not finish or threw).
Collapsing those into one number would hide which half of the pipeline broke.
"""
from __future__ import annotations
import argparse, json, os, shutil, subprocess, sys
from collections import Counter
from pathlib import Path

from common import (BUILD, DAFNY_VERSION, DATA, PRELUDE, SOLUTIONS, event, log,
                    read_jsonl, write_json, write_jsonl)

DAFNY = shutil.which("dafny") or os.path.expanduser("~/.dotnet/tools/dafny")
SOLVER = shutil.which("z3") or "/usr/local/bin/z3"


def conv_expr(dtype: str, v: str) -> str:
    """Python expression converting `v` into the Dafny runtime representation."""
    dtype = dtype.strip()
    if dtype == "int":
        return f"int({v})"
    if dtype == "bool":
        return f"bool({v})"
    if dtype == "real":
        return f"_mkreal({v})"
    if dtype == "string":
        return f"_dafny.Seq(map(_dafny.CodePoint, str({v})))"
    if dtype.startswith("seq<") and dtype.endswith(">"):
        inner = dtype[4:-1]
        return f"_dafny.Seq([{conv_expr(inner, '_e')} for _e in {v}])"
    if dtype.startswith("(") and dtype.endswith(")"):
        parts = _split_tuple(dtype[1:-1])
        return "(" + ", ".join(conv_expr(p, f"{v}[{i}]")
                               for i, p in enumerate(parts)) + ",)"
    raise ValueError(f"no marshaller for Dafny type {dtype!r}")


def _split_tuple(s: str):
    """Split "int, seq<int>" on top-level commas."""
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch in "<(":
            depth += 1
        elif ch in ">)":
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur)
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur)
    return [x.strip() for x in out]


HARNESS = '''\
"""Generated. Runs one solution against a batch of tests in a single process."""
import json, signal, sys, traceback
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

tests = json.load(open({testspath!r}, encoding="utf-8"))
results = []
for t in tests:
    signal.alarm({per_test})
    try:
        inp = Input.from_str(t["input"])
        out = module_.default__.Solve({args})
        got = out.VerbatimString(False)
        ok = got.rstrip() == t["output"].rstrip()
        results.append({{"status": "pass" if ok else "fail",
                         "got": None if ok else got[:400]}})
    except _Timeout:
        results.append({{"status": "timeout"}})
    except Exception as e:
        results.append({{"status": "error",
                         "error": f"{{type(e).__name__}}: {{e}}"[:300]}})
    finally:
        signal.alarm(0)

json.dump(results, sys.stdout)
'''


def build_one(dfy: Path, workdir: Path):
    """dafny translate py -> (pydir, error). Never verifies: the gate is tests."""
    workdir.mkdir(parents=True, exist_ok=True)
    out = workdir / "out"
    p = subprocess.run(
        [DAFNY, "translate", "py", str(dfy), "--no-verify",
         "--include-runtime", "--solver-path", SOLVER, "--output", str(out)],
        capture_output=True, text=True, timeout=300)
    pydir = workdir / "out-py"
    if p.returncode != 0 or not (pydir / "module_.py").exists():
        return None, (p.stdout + p.stderr).strip()[:1500]
    return pydir, None


def run_tests(task, sig, pydir, workdir, tiers, per_test, batch_timeout):
    tests = []
    for tier in tiers:
        for t in task["tests"].get(tier, []):
            tests.append({"input": t["input"], "output": t["output"], "tier": tier})
    if not tests:
        return [], "no tests in the requested tiers"

    (workdir / "dataclass.py").write_text(task["dataclass_code"], encoding="utf-8")
    (workdir / "tests.json").write_text(json.dumps(tests), encoding="utf-8")
    args = ", ".join(conv_expr(p["dafny_type"], f'inp.{p["py_name"]}')
                     for p in sig["params"])
    (workdir / "harness.py").write_text(
        HARNESS.format(pydir=str(pydir), dcpath=str(workdir / "dataclass.py"),
                       testspath=str(workdir / "tests.json"),
                       per_test=per_test, args=args),
        encoding="utf-8")

    try:
        p = subprocess.run([sys.executable, str(workdir / "harness.py")],
                           capture_output=True, text=True, timeout=batch_timeout)
    except subprocess.TimeoutExpired:
        return None, f"harness exceeded {batch_timeout}s"
    if p.returncode != 0:
        return None, (p.stdout + p.stderr).strip()[:1500]
    try:
        res = json.loads(p.stdout)
    except json.JSONDecodeError:
        return None, f"harness produced non-JSON: {p.stdout[:400]}"
    for r, t in zip(res, tests):
        r["tier"] = t["tier"]
    return res, None


def validate(only=None, tiers=("public_tests", "private_tests"),
             per_test=10, batch_timeout=600, limit=None, solutions_dir=None,
             out_prefix=""):
    tasks = {t["solution_id"]: t for t in read_jsonl(DATA / "tasks.jsonl")}
    sigs = {s["problem_id"]: s for s in read_jsonl(DATA / "signatures.jsonl")}

    root = Path(solutions_dir) if solutions_dir else SOLUTIONS
    targets = []
    for sid, t in tasks.items():
        dfy = root / t["problem_id"] / f"{sid}.dfy"
        if not dfy.exists():
            continue
        if only and sid not in only:
            continue
        targets.append((t, dfy))
    targets.sort(key=lambda x: (int(x[0]["problem_id"]), x[0]["solution_id"]))
    if limit:
        targets = targets[:limit]
    log(f"validating {len(targets)} solutions "
        f"(tiers={'+'.join(tiers)}, per-test {per_test}s)")

    rows, tally = [], Counter()
    for t, dfy in targets:
        sid = t["solution_id"]
        sig = sigs[t["problem_id"]]
        work = BUILD / (out_prefix + sid)
        work.mkdir(parents=True, exist_ok=True)
        rec = {"solution_id": sid, "problem_id": t["problem_id"],
               "problem_name": t["problem_name"],
               "time_complexity_inferred": t["time_complexity_inferred"],
               "dafny_version": DAFNY_VERSION, "dfy_path": str(dfy)}

        pydir, err = build_one(dfy, work)
        if err:
            rec.update(status="build", error=err)
            rows.append(rec); tally["build"] += 1
            log(f"  {sid:>10}  BUILD FAILED")
            continue

        res, err = run_tests(t, sig, pydir, work, tiers, per_test, batch_timeout)
        if err:
            rec.update(status="error", error=err)
            rows.append(rec); tally["error"] += 1
            log(f"  {sid:>10}  HARNESS ERROR  {err.splitlines()[0][:80] if err else ''}")
            continue

        c = Counter(r["status"] for r in res)
        rec.update(status="valid" if c["pass"] == len(res) else "fail",
                   tests_total=len(res), tests_passed=c["pass"],
                   tests_failed=c["fail"], tests_timeout=c["timeout"],
                   tests_error=c["error"],
                   first_failure=next((r for r in res if r["status"] != "pass"), None))
        rows.append(rec); tally[rec["status"]] += 1
        log(f"  {sid:>10}  {rec['status'].upper():<6} {c['pass']}/{len(res)} tests")

    write_jsonl(DATA / f"{out_prefix}validation.jsonl", rows)
    summary = {"dafny_version": DAFNY_VERSION, "tiers": list(tiers),
               "validated": len(rows), **{k: tally[k] for k in
               ("valid", "fail", "build", "error")}}
    write_json(DATA / f"{out_prefix}validation_summary.json", summary)
    event("validate", **summary)
    log(f"summary: {dict(tally)}")
    return rows


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", nargs="*", help="solution_ids to validate")
    ap.add_argument("--generated", action="store_true",
                    help="also run the generated_tests tier")
    ap.add_argument("--per-test", type=int, default=10)
    ap.add_argument("--limit", type=int)
    ap.add_argument("--out-prefix", default="")
    a = ap.parse_args()
    tiers = ["public_tests", "private_tests"] + (["generated_tests"] if a.generated else [])
    validate(only=set(a.only) if a.only else None, tiers=tuple(tiers),
             per_test=a.per_test, limit=a.limit, out_prefix=a.out_prefix)
