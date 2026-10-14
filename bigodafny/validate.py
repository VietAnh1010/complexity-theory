"""Compile a .dfy to Python, drive it with BigOBench's own parser, diff stdout.

A row is valid only if it translates AND every executed test matches. The three
failure modes are recorded separately: `build` (Dafny rejected it), `fail` (it
ran and printed the wrong thing), `timeout`/`error` (it did not finish or threw).
Collapsing those into one number would hide which half of the pipeline broke.
"""
from __future__ import annotations
import argparse, json, shutil, subprocess, sys, tempfile
from concurrent.futures import ProcessPoolExecutor
from collections import Counter
from pathlib import Path

from common import (WORKERS, BUILD, DAFNY_VERSION, DATA, OUT, PRELUDE, UNSCREENED, SOLUTIONS,
                    UNVERIFIED, log, read_jsonl, write_json,
                    write_jsonl, DISPUTED, ROOT, UNSURE, in_spec)

DAFNY = "dafny"   # on PATH; dafny finds z3 on PATH itself


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
         "--include-runtime", "--output", str(out)],
        capture_output=True, text=True, timeout=300)
    pydir = workdir / "out-py"
    if p.returncode != 0 or not (pydir / "module_.py").exists():
        return None, (p.stdout + p.stderr).strip()[:1500]
    return pydir, None


def run_tests(task, sig, pydir, workdir, tiers, per_test, batch_timeout):
    tests = []
    for tier in tiers:
        for t in task["tests"].get(tier, []):
            if in_spec(task, t["input"]):
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

    # Every test carries its own `per_test` alarm, so a batch of n tests can
    # legitimately spend per_test*n seconds before any of them is a bug. A fixed
    # wall budget below that discards the whole row, including the tests that
    # already passed -- difftest.py lost 91 agreeing comparisons on `1501_224`
    # exactly this way. Take whichever of the two budgets is larger; the caller's
    # `batch_timeout` stays a floor, not a ceiling.
    budget = max(batch_timeout, 60 + per_test * max(1, len(tests)))
    try:
        p = subprocess.run([sys.executable, str(workdir / "harness.py")],
                           capture_output=True, text=True, timeout=budget)
    except subprocess.TimeoutExpired:
        return None, f"harness exceeded {budget}s"
    if p.returncode != 0:
        return None, (p.stdout + p.stderr).strip()[:1500]
    try:
        res = json.loads(p.stdout)
    except json.JSONDecodeError:
        return None, f"harness produced non-JSON: {p.stdout[:400]}"
    for r, t in zip(res, tests):
        r["tier"] = t["tier"]
    return res, None


TIERS = ("public_tests", "private_tests")


def check_one(job):
    t, dfy, sig, tiers, per_test, batch_timeout, out_prefix = job
    sid = t["solution_id"]
    work = BUILD / (out_prefix + sid)
    work.mkdir(parents=True, exist_ok=True)
    rec = {"solution_id": sid, "problem_id": t["problem_id"],
           "problem_name": t["problem_name"],
           "time_complexity_inferred": t["time_complexity_inferred"],
           "dafny_version": DAFNY_VERSION, "dfy_path": str(dfy.relative_to(ROOT) if dfy.is_relative_to(ROOT)
                            else dfy)}

    pydir, err = build_one(dfy, work)
    if err:
        return {**rec, "status": "build", "error": err}

    res, err = run_tests(t, sig, pydir, work, tiers, per_test, batch_timeout)
    if err:
        return {**rec, "status": "error", "error": err}

    c = Counter(r["status"] for r in res)
    oos = sum(not in_spec(t, x["input"]) for k in tiers for x in t["tests"].get(k, []))
    if oos:
        rec["tests_out_of_spec"] = oos
    rec.update(status="valid" if c["pass"] == len(res) else "fail",
               tests_total=len(res), tests_passed=c["pass"],
               tests_failed=c["fail"], tests_timeout=c["timeout"],
               tests_error=c["error"],
               first_failure=next((r for r in res if r["status"] != "pass"), None))
    return rec


def validate(only=None, per_test=30, batch_timeout=900, solutions_dir=None,
             out_prefix="", workers=WORKERS):
    tiers = TIERS
    tasks = {t["solution_id"]: t for t in read_jsonl(DATA / "tasks.jsonl")}
    sigs = {s["problem_id"]: s for s in read_jsonl(DATA / "signatures.jsonl")}

    # This gate judges the `strict` tier and no other. Its whole question is
    # "does stdout match BigOBench's STORED output", which is the wrong
    # question for the 100 `loose` rows -- their problems accept several
    # answers, so even the original Python fails a byte-diff. Running on them
    # produces `fail` records that measure the checker, not the translation.
    #
    # Nothing enforced that. A bare `validate.py` swept all 636 translated rows
    # and wrote 101 `fail`s, of which 97 were loose rows behaving correctly;
    # the record it replaced had been built from a hand-filtered list, so the
    # canonical file was not reproducible from this tool's own CLI. It is now.
    ds = DATA / "dataset.jsonl"
    split = ({r["solution_id"]: r["split"] for r in read_jsonl(ds)}
             if ds.exists() else {})
    if not split:
        log("warning: data/dataset.jsonl absent, cannot filter to the strict "
            "tier; validating every translated row")

    roots = ([Path(solutions_dir)] if solutions_dir
             else [SOLUTIONS, UNSCREENED, UNVERIFIED, DISPUTED, UNSURE])
    targets, skipped = [], Counter()
    for sid, t in tasks.items():
        dfy = next((r / t["problem_id"] / f"{sid}.dfy" for r in roots
                    if (r / t["problem_id"] / f"{sid}.dfy").exists()), None)
        if dfy is None:
            continue
        if only and sid not in only:
            continue
        # An explicit --only or --solutions-dir is a deliberate request; only
        # the unfiltered sweep is narrowed to the tier this gate answers for.
        if (not only and not solutions_dir
                and split.get(sid, "strict") != "strict"):
            skipped[split[sid]] += 1
            continue
        targets.append((t, dfy))
    if skipped:
        log(f"skipping {sum(skipped.values())} rows this gate does not judge: "
            + ", ".join(f"{v} {k}" for k, v in sorted(skipped.items()))
            + "  (difftest.py --loose is the loose tier's gate)")
    targets.sort(key=lambda x: (int(x[0]["problem_id"]), x[0]["solution_id"]))
    log(f"validating {len(targets)} solutions "
        f"(tiers={'+'.join(tiers)}, per-test {per_test}s)")

    jobs = [(t, dfy, sigs[t["problem_id"]], tiers, per_test, batch_timeout,
             out_prefix) for t, dfy in targets]
    rows = []
    # Rows are independent; map keeps them in target order.
    with ProcessPoolExecutor(max_workers=workers) as ex:
        for rec in ex.map(check_one, jobs):
            rows.append(rec)
            log(f"  {rec['solution_id']:>10}  {rec['status'].upper():<6} "
                + (f"{rec['tests_passed']}/{rec['tests_total']} tests"
                   if "tests_total" in rec else (rec.get("error") or "").splitlines()[0][:80]
                   if rec.get("error") else ""))
    # Parallel load can push a test past its time limit (577_509, 1738_180
    # pass alone). Re-check every non-valid row alone; only that result counts.
    for i, rec in enumerate(rows):
        if rec["status"] != "valid":
            log(f"  {rec['solution_id']:>10}  {rec['status']} under load; re-checking alone")
            rows[i] = check_one(jobs[i])
            log(f"  {rec['solution_id']:>10}  alone: {rows[i]['status'].upper()}")
    tally = Counter(r["status"] for r in rows)

    # A partial run must never replace the canonical record: one
    # `validate.py --only X` once left data/validation.jsonl holding a single
    # row where 532 had been (difftest.py had the same defect). Any subset --
    # `--only` or `--solutions-dir` -- is a spot check and always writes a
    # prefixed file; `--out-prefix` only names it (default `partial_`).
    if not out_prefix and (only or solutions_dir):
        out_prefix = "partial_"
    if out_prefix:
        log(f"spot check: writing out/{out_prefix}validation.jsonl, not the "
            "canonical data/validation.jsonl")

    write_jsonl((OUT if out_prefix else DATA) / f"{out_prefix}validation.jsonl", rows,
                key=None if out_prefix else "solution_id")
    summary = {"dafny_version": DAFNY_VERSION, "tiers": list(tiers),
               "validated": len(rows), **{k: tally[k] for k in
               ("valid", "fail", "build", "error")}}
    write_json(OUT / f"{out_prefix}validation_summary.json", summary)
    log(f"summary: {dict(tally)}")
    return rows


# --self-test borrows one known-good row and breaks it in the two ways that
# matter. A gate only ever run on correct input is untested: if a wrong answer
# came back `build`, or a build error `fail`, the failure counts would mean
# nothing. The row moves between directories as audits reclassify it, so look
# wherever it currently lives.
GATE_ROW = ("5", "5_100")
GATE_CASES = (
    ("wrong", "fail", ('output := IntToString(m) + "\\n";',
                       'output := IntToString(m + 1) + "\\n";')),
    ("broken", "build", ("var m, k := n, 1;", "var m, k := n, ;")),
)


def self_test():
    pid, sid = GATE_ROW
    src = next((r / pid / f"{sid}.dfy" for r in
                (SOLUTIONS, DISPUTED, UNSCREENED, UNVERIFIED, UNSURE)
                if (r / pid / f"{sid}.dfy").exists()), None)
    if src is None:
        raise SystemExit(f"test row {sid} is in no solutions* directory")
    bad = 0
    for name, want, (old, new) in GATE_CASES:
        with tempfile.TemporaryDirectory() as d:
            # Mirror the tree: the row's `include "../../prelude.dfy"` must resolve.
            shutil.copy(PRELUDE, Path(d) / "prelude.dfy")
            dst = Path(d) / "solutions" / pid
            dst.mkdir(parents=True)
            (dst / f"{sid}.dfy").write_text(
                src.read_text(encoding="utf-8").replace(old, new), encoding="utf-8")
            rows = validate(only={sid}, solutions_dir=dst.parent,
                            out_prefix=f"self_test_{name}_")
        got = rows[0]["status"] if rows else "no-rows"
        bad += got != want
        log(f"{'ok  ' if got == want else 'FAIL'} {name}: expected {want!r}, got {got!r}")
    # The unmodified row must still be valid, or the two cases prove nothing.
    rows = validate(only={sid}, out_prefix="self_test_control_")
    got = rows[0]["status"] if rows else "no-rows"
    bad += got != "valid"
    log(f"{'ok  ' if got == 'valid' else 'FAIL'} control: expected 'valid', got {got!r}")
    log("SELF-TEST PASSED" if not bad else f"SELF-TEST FAILED ({bad})")
    return 1 if bad else 0


def main(argv=None):
    ap = argparse.ArgumentParser(prog="validate.py")
    ap.add_argument("--only", nargs="*", help="solution_ids to validate "
                    "(a spot check: never writes the canonical record)")
    ap.add_argument("--time-limit-per-test", type=int, default=30,
                    help="seconds per test (default 30)")
    ap.add_argument("--out-prefix", default="",
                    help="name the spot-check output out/<prefix>validation.jsonl "
                         "(default partial_)")
    ap.add_argument("--solutions-dir", help="look for rows only in this directory "
                    "(a spot check: never writes the canonical record)")
    ap.add_argument("--workers", type=int, default=WORKERS)
    ap.add_argument("--self-test", action="store_true",
                    help="test validate.py itself: a wrong answer must come back fail, "
                         "a compile error build, the untouched row valid")
    a = ap.parse_args(argv)
    if a.self_test:
        return self_test()
    validate(only=set(a.only) if a.only else None,
             per_test=a.time_limit_per_test, out_prefix=a.out_prefix,
             solutions_dir=a.solutions_dir, workers=a.workers)
    return 0


if __name__ == "__main__":
    sys.exit(main())
