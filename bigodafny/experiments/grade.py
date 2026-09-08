"""Grade one agent's work on one example. Five gates, recorded separately.

The gate that matters most is not the one about the label. An agent can make
any bound true by changing the algorithm -- replace a quadratic scan with a
closed form and every test still passes, because the answers are the same. That
is the exact failure `bigodafny/CLAUDE.md` records under "translate the
algorithm, not just the behaviour", and a behaviour test cannot see it.

So `skeleton` compares the **compiled** control flow. Dafny erases `ghost`
material, so a legitimate proof leaves the emitted Python's loops and branches
untouched; it may add plain local witnesses, which show up as assignments and
are counted, not rejected. An algorithm swap changes the loops and is caught.

    python3 experiments/grade.py --run-id pilot1 --arm blind
    python3 experiments/grade.py --run-id pilot1 --arm both --no-behaviour
"""
from __future__ import annotations
import argparse, difflib, json, os, re, subprocess, sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parent))
from common import BUILD, DATA, read_jsonl, log                   # noqa: E402
import validate as V                                              # noqa: E402
import difftest as DT                                             # noqa: E402
from bound import classify, extract_ensures, same_class           # noqa: E402
from stage import CX_ROOT                                         # noqa: E402

HERE = Path(__file__).resolve().parent
RUNS = HERE / "runs"
SOLVER = "/usr/local/bin/z3"
DAFNY = V.DAFNY

# `grep -q "0 errors"` also matches "10 errors" and "20 errors". That mistake
# reported a 5-error file as clean in this project once already.
VERIFIED_RE = re.compile(r"verifier finished with (\d+) verified, (\d+) error")
CONTROL = ("while ", "for ", "if ", "elif ", "else", "def ", "return",
           "break", "continue", "try", "except", "with ")


def dafny_verify(path: Path, seconds=60):
    p = subprocess.run(
        [DAFNY, "verify", str(path.name), "--solver-path", SOLVER,
         "--verification-time-limit", str(seconds), "--error-limit", "0"],
        capture_output=True, text=True, timeout=seconds * 20 + 300,
        cwd=str(path.parent))
    out = p.stdout + p.stderr
    m = VERIFIED_RE.search(out)
    # A lemma that times out proves nothing, yet its callers can still report
    # verified. Seen in this project on a bitvector cast bound.
    timeout = bool(re.search(r"timed out|Verification out of resource", out, re.I))
    return {
        "verified_count": int(m.group(1)) if m else 0,
        "error_count": int(m.group(2)) if m else -1,
        "timeout": timeout,
        "ok": bool(m) and int(m.group(2)) == 0 and not timeout,
        "tail": out.strip().splitlines()[-4:],
    }


# Dafny numbers its generated locals in declaration order, so inserting one
# ghost variable renumbers every later `d_3_j_` to `d_4_j_`. That is not a
# change of algorithm, and normalising it away is what lets the gate be strict
# about everything else.
RENUM = re.compile(r"\b(d|rhs|let|pat|source)_?\d+_")


def skeleton(py_text):
    return [RENUM.sub(r"\1_", l.strip()) for l in py_text.splitlines()
            if any(l.strip().startswith(k) for k in CONTROL)]


def compiled(dfy: Path, work: Path):
    pydir, err = V.build_one(dfy, work)
    if err:
        return None, err
    return (pydir / "module_.py").read_text(encoding="utf-8"), None


def behaviour(sid, task, sig, dfy: Path, work: Path, split):
    """The row's own gate: stored-output diff for strict, self-diff for loose."""
    if split == "loose":
        # difftest resolves the .dfy from the repo roots; point it at ours
        # instead. The comparison itself is untouched -- a gate must not be
        # loosened by the thing it judges.
        old = DT.find
        DT.find = lambda s, p, _d=dfy: _d
        try:
            DT.init({sid: task}, {task["problem_id"]: sig})
            rec = DT.one((sid, ("public_tests", "private_tests")))
        finally:
            DT.find = old
        return {"gate": rec.get("status") == "agrees", "detail": rec.get("status"),
                "passed": rec.get("agree"), "total": rec.get("comparable")}
    if split == "unvalidatable":
        return {"gate": None, "detail": "unvalidatable-split"}
    pydir, err = V.build_one(dfy, work)
    if err:
        return {"gate": False, "detail": "build: " + err[:200]}
    res, err = V.run_tests(task, sig, pydir, work,
                           ("public_tests", "private_tests"), 30, 900)
    if err:
        return {"gate": False, "detail": "harness: " + err[:200]}
    npass = sum(1 for r in res if r["status"] == "pass")
    return {"gate": npass == len(res), "detail": f"{npass}/{len(res)}",
            "passed": npass, "total": len(res)}


def grade_one(run_id, arm, ex, task, sig, do_behaviour=True):
    d = CX_ROOT / run_id / arm / ex["sid"]
    rec = {"run_id": run_id, "arm": arm, "sid": ex["sid"],
           "problem_id": ex["problem_id"], "label": ex["label"],
           "split": ex["split"], "difficulty_static": ex["difficulty_static"]}

    res_path = d / "result.json"
    if res_path.exists():
        try:
            rec["result"] = json.loads(res_path.read_text())
        except Exception as e:
            rec["result"] = {"_parse_error": str(e)[:200]}
    else:
        rec["result"] = None

    cur, orig = d / "task.dfy", d / ".original.dfy"
    if not cur.exists():
        rec["status"] = "missing-file"
        return rec
    text = cur.read_text(encoding="utf-8")
    rec["touched"] = text != orig.read_text(encoding="utf-8")

    # 1 -- does it verify
    rec["gate_verify"] = dafny_verify(cur)
    # 2 -- no assume, including {:axiom}
    rec["assumes"] = len(re.findall(r"\bassume\b", text))
    rec["gate_no_assume"] = rec["assumes"] == 0
    # 3 -- compiled control flow unchanged
    work = BUILD / f"grade_{run_id}_{arm}_{ex['sid']}"
    a, ea = compiled(orig, work / "orig")
    b, eb = compiled(cur, work / "cur")
    if a is None or b is None:
        rec["gate_skeleton"] = False
        rec["skeleton_detail"] = (ea or eb or "")[:200]
    else:
        sa, sb = skeleton(a), skeleton(b)
        rec["gate_skeleton"] = sa == sb
        rec["code_identical"] = a == b
        rec["added_exec_lines"] = len(b.splitlines()) - len(a.splitlines())
        if sa != sb:
            rec["skeleton_detail"] = "\n".join(
                list(difflib.unified_diff(sa, sb, lineterm=""))[:20])
    # 4 -- behaviour on the row's own gate
    rec["gate_behaviour"] = (behaviour(ex["sid"], task, sig, cur, work / "beh",
                                       ex["split"]) if do_behaviour else None)
    # 5 -- what class did it actually prove
    ens = extract_ensures(text)
    rec["bound_ensures"] = ens
    if ens:
        cls, shape, det = classify(ens)
        rec["bound_class"], rec["bound_shape"], rec["bound_detail"] = cls, shape, det
    else:
        rec["bound_class"], rec["bound_shape"] = None, None

    ok = (rec["gate_verify"]["ok"] and rec["gate_no_assume"]
          and rec["gate_skeleton"] and bool(ens)
          and (rec["gate_behaviour"] is None
               or rec["gate_behaviour"]["gate"] is not False))
    rec["gate_all"] = ok
    rec["proved"] = ok
    rec["label_match"] = same_class(rec["bound_class"], ex["label"]) if ok else None
    if arm == "blind" and rec["result"]:
        g = (rec["result"] or {}).get("guess")
        rec["guess"] = g
        rec["guess_correct"] = same_class(g, ex["label"]) if g else None
    rec["status"] = "graded"
    return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--run-id", required=True)
    ap.add_argument("--arm", choices=["labeled", "blind", "both"], default="both")
    ap.add_argument("--only", nargs="*")
    ap.add_argument("--no-behaviour", action="store_true")
    a = ap.parse_args()

    man = json.loads((HERE / "manifest.json").read_text())
    tasks = {t["solution_id"]: t for t in read_jsonl(DATA / "tasks.jsonl")}
    sigs = {s["problem_id"]: s for s in read_jsonl(DATA / "signatures.jsonl")}
    arms = ["labeled", "blind"] if a.arm == "both" else [a.arm]

    out, skipped = [], 0
    for arm in arms:
        for ex in man["examples"]:
            if a.only and ex["sid"] not in a.only:
                continue
            d = CX_ROOT / a.run_id / arm / ex["sid"]
            if not (d / "task.dfy").exists():
                continue
            # Staging leaves every example with a task.dfy, so "the file
            # exists" is not evidence an agent worked on it. An example with
            # no result.json AND an untouched file was never attempted; the
            # first grading run spent half an hour compiling 96 of those.
            if not (d / "result.json").exists() and \
                    (d / "task.dfy").read_bytes() == (d / ".original.dfy").read_bytes():
                skipped += 1
                continue
            r = grade_one(a.run_id, arm, ex, tasks[ex["sid"]],
                          sigs[ex["problem_id"]], not a.no_behaviour)
            out.append(r)
            log(f"  {arm:8} {ex['sid']:10} verify={r.get('gate_verify',{}).get('ok')} "
                f"skel={r.get('gate_skeleton')} bound={r.get('bound_class')} "
                f"label={ex['label']} all={r.get('gate_all')}")

    (RUNS / a.run_id).mkdir(parents=True, exist_ok=True)
    p = RUNS / a.run_id / "graded.jsonl"
    existing = {(r["arm"], r["sid"]): r for r in
                (read_jsonl(p) if p.exists() else [])}
    for r in out:
        existing[(r["arm"], r["sid"])] = r
    rows = sorted(existing.values(), key=lambda r: (r["arm"], r["sid"]))
    p.write_text("".join(json.dumps(r, sort_keys=True) + "\n" for r in rows),
                 encoding="utf-8")
    print(f"graded {len(out)} -> {p}  (file now holds {len(rows)}); "
          f"{skipped} unattempted examples skipped")


if __name__ == "__main__":
    main()
