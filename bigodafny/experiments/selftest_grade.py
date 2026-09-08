"""Prove the grader works before trusting it on 200 agent runs.

A grader that has only ever seen correct input is untested -- the same rule
`selftest.py` applies to the validator. Three cases:

  1. the 12 finished proofs in solutions-verified/ and solutions-nlogn/ must
     pass every gate;
  2. a copy with `assume {:axiom} true;` added must be rejected -- it still
     reports 0 errors, which is exactly why the gate exists;
  3. a copy whose loops are replaced by an uncharged recursive helper must be
     rejected. It verifies, it passes every test, its output is identical, and
     it "proves" O(1) for an O(n+m) program. Only the compiled-skeleton gate
     sees it.

    python3 experiments/selftest_grade.py
"""
from __future__ import annotations
import json, shutil, sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parent))
from common import (DATA, INEXACT, NLOGN, PRELUDE, SOLUTIONS, UNVERIFIED,
                    VERIFIED, read_jsonl)                     # noqa: E402
from stage import CX_ROOT                                          # noqa: E402
import grade as G                                                  # noqa: E402

RUN = "selftest"

# The cheat: both loops replaced by a recursive helper that is never charged.
# Same output, same tests, verifies clean, claims constant time.
SABOTAGE_SRC = """
function OrAll(s: seq<int>): int
  requires forall i :: 0 <= i < |s| ==> s[i] >= 0
  decreases |s|
  ensures OrAll(s) >= 0
{ if |s| == 0 then 0 else BitOr(s[0], OrAll(s[1..])) }
"""


def stage_pair(run, arm, sid, original: Path, agent: Path):
    d = CX_ROOT / run / arm / sid
    d.mkdir(parents=True, exist_ok=True)
    fix = lambda t: t.replace('include "../../prelude.dfy"', 'include "prelude.dfy"')
    (d / ".original.dfy").write_text(fix(original.read_text()), encoding="utf-8")
    (d / "task.dfy").write_text(fix(agent.read_text()), encoding="utf-8")
    shutil.copyfile(PRELUDE, d / "prelude.dfy")
    return d


def make_sabotage_assume(d: Path):
    t = (d / "task.dfy").read_text()
    i = t.index("{", t.index("method Solve"))
    (d / "task.dfy").write_text(
        t[:i + 1] + "\n  assume {:axiom} true;\n" + t[i + 1:], encoding="utf-8")


def make_sabotage_algorithm(d: Path):
    """Replace 1029_119's two accumulation loops with an uncharged helper.

    Every test still passes and the output is identical -- that is the point.
    """
    t = (d / "task.dfy").read_text()
    head, _, rest = t.partition("method Solve")
    body = "method Solve" + rest
    sig = body[:body.index("ensures steps")]
    cheat = sig + """ensures steps <= 5
{
  steps := 1;
  var f1 := OrAll(a_list);
  var f2 := OrAll(b_list);
  steps := steps + 3;
  output := IntToString(f1 + f2);
  steps := steps + 1;
}
"""
    (d / "task.dfy").write_text(head + SABOTAGE_SRC + cheat, encoding="utf-8")


def main():
    tasks = {t["solution_id"]: t for t in read_jsonl(DATA / "tasks.jsonl")}
    sigs = {s["problem_id"]: s for s in read_jsonl(DATA / "signatures.jsonl")}
    ds = {r["solution_id"]: r for r in read_jsonl(DATA / "dataset.jsonl")}

    proofs = [(p, "nlogn" if NLOGN in p.parents else "verified")
              for d in (VERIFIED, NLOGN) for p in sorted(d.rglob("*.dfy"))]
    fails = []

    print("== case 1: the finished proofs must pass ==")
    for p, kind in proofs:
        sid = p.stem
        orig = next((r / ds[sid]["problem_id"] / f"{sid}.dfy"
                     for r in (SOLUTIONS, UNVERIFIED, INEXACT)
                     if (r / ds[sid]["problem_id"] / f"{sid}.dfy").exists()), None)
        if orig is None:
            print(f"  {sid:12} SKIP (no uninstrumented counterpart)")
            continue
        arm = f"proofs-{kind}"
        stage_pair(RUN, arm, sid, orig, p)
        ex = {"sid": sid, "problem_id": ds[sid]["problem_id"],
              "label": ds[sid]["time_complexity_inferred"],
              "split": ds[sid]["split"], "difficulty_static": 0}
        r = G.grade_one(RUN, arm, ex, tasks[sid], sigs[ex["problem_id"]], True)
        ok = r["gate_all"]
        beh = (r["gate_behaviour"] or {}).get("detail")
        print(f"  {sid:12} {kind:8} all={str(ok):5} verify={r['gate_verify']['ok']} "
              f"assume={r['gate_no_assume']} skel={r['gate_skeleton']} "
              f"beh={beh} bound={r['bound_class']} label={ex['label']}")
        if not ok:
            fails.append(f"case1 {sid} ({kind}) failed a gate")

    print("\n== case 2: an added `assume {:axiom}` must be rejected ==")
    sid = "5_100"
    d = stage_pair(RUN, "sabotage-assume", sid,
                   SOLUTIONS / ds[sid]["problem_id"] / f"{sid}.dfy",
                   VERIFIED / ds[sid]["problem_id"] / f"{sid}.dfy")
    make_sabotage_assume(d)
    ex = {"sid": sid, "problem_id": ds[sid]["problem_id"],
          "label": ds[sid]["time_complexity_inferred"],
          "split": ds[sid]["split"], "difficulty_static": 0}
    r = G.grade_one(RUN, "sabotage-assume", ex, tasks[sid],
                    sigs[ex["problem_id"]], False)
    print(f"  {sid:12} verify_ok={r['gate_verify']['ok']} assumes={r['assumes']} "
          f"no_assume={r['gate_no_assume']} all={r['gate_all']}")
    if r["gate_all"] or r["gate_no_assume"]:
        fails.append("case2 an added assume was not rejected")
    if not r["gate_verify"]["ok"]:
        fails.append("case2 file did not verify -- the test proves nothing")

    print("\n== case 3: loops replaced by an uncharged helper must be rejected ==")
    sid = "1029_119"
    d = stage_pair(RUN, "sabotage-algo", sid,
                   SOLUTIONS / ds[sid]["problem_id"] / f"{sid}.dfy",
                   VERIFIED / ds[sid]["problem_id"] / f"{sid}.dfy")
    make_sabotage_algorithm(d)
    ex = {"sid": sid, "problem_id": ds[sid]["problem_id"],
          "label": ds[sid]["time_complexity_inferred"],
          "split": ds[sid]["split"], "difficulty_static": 0}
    r = G.grade_one(RUN, "sabotage-algo", ex, tasks[sid], sigs[ex["problem_id"]], True)
    beh = (r["gate_behaviour"] or {}).get("detail")
    print(f"  {sid:12} verify_ok={r['gate_verify']['ok']} bound={r['bound_class']} "
          f"skel={r['gate_skeleton']} behaviour={beh} all={r['gate_all']}")
    if not r["gate_verify"]["ok"]:
        fails.append("case3 file did not verify -- the test proves nothing")
    if (r["gate_behaviour"] or {}).get("gate") is not True:
        fails.append("case3 behaviour did NOT pass -- then it is not the cheat "
                     "we mean to catch; behaviour tests were supposed to be blind to it")
    if r["gate_skeleton"]:
        fails.append("case3 the skeleton gate did not see the algorithm swap")
    if r["gate_all"]:
        fails.append("case3 a constant-time claim for a linear program was accepted")

    print("\n" + ("SELFTEST FAILED\n  " + "\n  ".join(fails)
                  if fails else "SELFTEST PASSED"))
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
