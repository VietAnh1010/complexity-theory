"""Join grading and trajectory into one table, then report it.

One row per (example, arm). `results.csv` is the artefact meant to outlive this
session; `RESULTS.md` is the reading of it.

The reading rules, fixed here rather than chosen after seeing numbers:

  * a proof counts only if it passed EVERY gate. A file that verifies but whose
    compiled control flow changed is not a proof of anything about the original
    program, and it is counted under `gate_failures`, never under `proved`.
  * a blind guess is scored against BigOBench's label, which is itself
    synthetic. Where a passing proof and the label disagree, both numbers are
    reported; the proof is the stronger statement and the disagreement is the
    finding, not an error to be smoothed.
  * an example whose agent tried to read the repo is reported separately and
    excluded from the headline accuracy.

    python3 experiments/aggregate.py --run-id pilot1
"""
from __future__ import annotations
import argparse, csv, json, sys
from collections import Counter, defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from bound import CLASSES, RANK, canon, direction, same_class     # noqa: E402

HERE = Path(__file__).resolve().parent
RUNS = HERE / "runs"

FIELDS = ["run_id", "arm", "sid", "problem_id", "label", "split", "model",
          "difficulty_static", "difficulty_measured", "drift", "drift_kind",
          "guess", "guess_correct", "verdict",
          "proved", "bound_class", "bound_shape", "bound_ensures",
          "label_match", "direction", "degenerate", "stub", "added_requires",
          "gate_verify", "gate_no_assume", "gate_skeleton", "gate_behaviour",
          "gate_requires", "requires_detail",
          "code_identical", "added_exec_lines", "assumes",
          "dafny_calls", "tool_calls", "wall_s", "output_tokens",
          "leak_attempts", "attempts", "agent_id", "notes"]


def degenerate(bound_class, ex):
    """A constant bound on a program that loops over its input.

    If the problem statement caps a value numerically -- `1 <= n <= 10^9` --
    then every loop it controls runs a bounded number of times and `steps <= 2e10`
    is true, verifiable, and says nothing. One blind agent proved exactly that
    for a row whose labeled counterpart proved `steps <= n + 3`.

    The guide tells agents to fold a statement's cap into the constant when a
    loop is otherwise unbounded, which is right; folding it in until the bound
    stops mentioning the input at all is where it becomes vacuous. Flagged, and
    never counted as refuting a label.
    """
    if bound_class != "O(1)" or not ex:
        return False
    return (ex.get("features", {}).get("loops", 0) or 0) > 0


def measured_difficulty(dafny_calls, wall_s, proved):
    """1..5 from what the run actually cost. Declared here, not tuned later.

    Deliberately crude: the point is to compare it against `difficulty_static`,
    which was fixed before any agent ran, not to be a precise cost model.
    """
    d = 1
    d += 1 if (dafny_calls or 0) >= 4 else 0
    d += 1 if (dafny_calls or 0) >= 10 else 0
    d += 1 if (wall_s or 0) >= 600 else 0
    d += 0 if proved else 1
    return max(1, min(5, d))


def load(run_id):
    rd = RUNS / run_id
    graded = [json.loads(l) for l in
              (rd / "graded.jsonl").read_text().splitlines() if l.strip()]
    traj = json.loads((rd / "trajectory.json").read_text()) \
        if (rd / "trajectory.json").exists() else []
    # Keyed by (arm, sid), not sid. Keyed by sid alone, the labeled rows
    # silently inherited the blind agent's tool counts for the same example.
    # Several agents can touch one (arm, sid) -- an example that was retried --
    # so their effort is summed and the attempt count recorded.
    by_key = {}
    for ag in traj:
        for sid, v in ag["per_example"].items():
            by_key.setdefault((ag.get("arm", "?"), sid), []).append((ag, v))
    return graded, by_key


def combine(entries):
    """Sum the effort of every agent that worked one (arm, sid)."""
    if not entries:
        return {}, {}
    agents = [a for a, _ in entries]
    vs = [v for _, v in entries]
    tot = {
        "tool_calls": sum(v.get("tool_calls") or 0 for v in vs),
        "dafny_calls": sum(v.get("dafny_calls") or 0 for v in vs),
        "wall_s": round(sum(v.get("wall_s") or 0 for v in vs), 1),
        "leak_attempts": sum(v.get("leak_attempts") or 0 for v in vs),
        "attempts": len(vs),
    }
    ag = {"model": agents[0].get("model"),
          "agent_id": ",".join(a["agent_id"][6:14] for a in agents),
          "output_tokens": sum(a.get("output_tokens") or 0 for a in agents)}
    return tot, ag


def rows(run_id):
    graded, traj = load(run_id)
    man = {e["sid"]: e for e in
           json.loads((HERE / "manifest.json").read_text())["examples"]}
    out = []
    for g in graded:
        res = g.get("result") or {}
        t, ag = combine(traj.get((g["arm"], g["sid"]), []))
        proved = bool(g.get("gate_all"))
        dr = (man.get(g["sid"], {}) or {}).get("drift", {})
        beh = g.get("gate_behaviour") or {}
        r = {
            "run_id": g["run_id"], "arm": g["arm"], "sid": g["sid"],
            "problem_id": g["problem_id"], "label": g["label"],
            "split": g["split"], "model": (ag or {}).get("model"),
            "difficulty_static": g["difficulty_static"],
            "drift": bool(dr.get("drift_slower") or dr.get("drift_sort")),
            "drift_kind": ("append-in-loop" if dr.get("drift_slower") else "")
                          + ("|" if dr.get("drift_slower") and dr.get("drift_sort") else "")
                          + ("sort-mismatch" if dr.get("drift_sort") else ""),
            "difficulty_measured": measured_difficulty(
                (t or {}).get("dafny_calls"), (t or {}).get("wall_s"), proved),
            "guess": g.get("guess") or res.get("guess"),
            "guess_correct": g.get("guess_correct"),
            "verdict": res.get("verdict"),
            "proved": proved,
            "bound_class": g.get("bound_class"),
            "bound_shape": g.get("bound_shape"),
            "bound_ensures": g.get("bound_ensures"),
            "label_match": g.get("label_match"),
            "direction": direction(g.get("bound_class"), g["label"]),
            "degenerate": degenerate(g.get("bound_class"), man.get(g["sid"])),
            # The write-result-first rule means an agent that was cut off, or
            # is still running, leaves a `gave_up` stub that is
            # indistinguishable in the CSV from a real give-up. It is not one:
            # the file was never touched. Counted apart, or the proof-rate
            # denominator silently absorbs every rate-limit casualty as a
            # failure.
            "stub": not g.get("touched") and not g.get("bound_ensures"),
            "added_requires": "; ".join(res.get("added_requires") or []),
            "gate_verify": (g.get("gate_verify") or {}).get("ok"),
            "gate_no_assume": g.get("gate_no_assume"),
            "gate_skeleton": g.get("gate_skeleton"),
            "gate_behaviour": beh.get("gate"),
            "gate_requires": (g.get("gate_requires") or {}).get("gate"),
            "requires_detail": (g.get("gate_requires") or {}).get("detail"),
            "code_identical": g.get("code_identical"),
            "added_exec_lines": g.get("added_exec_lines"),
            "assumes": g.get("assumes"),
            "dafny_calls": (t or {}).get("dafny_calls"),
            "tool_calls": (t or {}).get("tool_calls"),
            "wall_s": (t or {}).get("wall_s"),
            "output_tokens": (ag or {}).get("output_tokens"),
            "leak_attempts": (t or {}).get("leak_attempts", 0),
            "attempts": (t or {}).get("attempts", 0),
            "agent_id": (ag or {}).get("agent_id"),
            "notes": (res.get("notes") or "").replace("\n", " ")[:300],
        }
        out.append(r)
    out.sort(key=lambda r: (r["arm"], r["sid"]))
    return out


def report(rs):
    stubs = [r for r in rs if r["stub"]]
    scorable = [r for r in rs if not r["stub"]]
    L = [r for r in scorable if r["arm"] == "labeled"]
    # Proof rate excludes stubs; the GUESS does not. The blind arm writes its
    # guess before attempting any proof, on purpose, so an agent cut off
    # mid-proof still left a real, committed answer to the question this
    # experiment is actually asking. Dropping those would throw away the
    # measurement to tidy up the denominator of a different one.
    B = [r for r in scorable if r["arm"] == "blind"]
    B_guess = [r for r in rs if r["arm"] == "blind" and r["guess"]]
    o = []
    w = o.append

    w("# Complexity-proving experiment\n")
    w(f"{len(rs)} runs scored: {len(L)} labeled, {len(B)} blind.\n")
    if stubs:
        w(f"{len(stubs)} further example(s) hold only a `gave_up` stub with an")
        w("untouched file -- an agent cut off by a rate limit, or still running.")
        w("Not a give-up, and not counted in any rate below: "
          + ", ".join(f"{r['arm']}/`{r['sid']}`" for r in stubs) + "\n")

    w("## Proof rate\n")
    w("| arm | attempted | proved | verified but gate-failed | no bound |")
    w("|---|---|---|---|---|")
    for name, arm in (("labeled", L), ("blind", B)):
        pr = sum(1 for r in arm if r["proved"])
        gf = sum(1 for r in arm if r["gate_verify"] and not r["proved"])
        nb = sum(1 for r in arm if not r["bound_ensures"])
        w(f"| {name} | {len(arm)} | {pr} | {gf} | {nb} |")
    w("")

    w("## Blind arm: did it name the class\n")
    clean = [r for r in B_guess if not r["leak_attempts"]]
    scored = [r for r in clean if r["guess"]]
    ok = sum(1 for r in scored if r["guess_correct"])
    w(f"- guessed on {len(scored)} of {len(B_guess)} blind examples "
      f"({len(B_guess) - len(clean)} excluded for a leak attempt); "
      f"{sum(1 for r in B_guess if r['stub'])} of these come from an agent cut "
      f"off before it could finish the proof, whose guess is still valid")
    if scored:
        w(f"- correct: **{ok}/{len(scored)}** = {100*ok/len(scored):.0f}%")
    w("")
    per = defaultdict(lambda: [0, 0])
    for r in scored:
        per[r["label"]][1] += 1
        per[r["label"]][0] += 1 if r["guess_correct"] else 0
    if per:
        w("| true class | guessed right | n |")
        w("|---|---|---|")
        for k in CLASSES:
            if k in per:
                w(f"| `{k}` | {per[k][0]} | {per[k][1]} |")
        w("")
        w("### Confusion (rows = true, cols = guessed)\n")
        seen = sorted({r["guess"] for r in scored if r["guess"]},
                      key=lambda x: CLASSES.index(x) if x in CLASSES else 99)
        w("| true \\ guess | " + " | ".join(f"`{c}`" for c in seen) + " |")
        w("|" + "---|" * (len(seen) + 1))
        for k in CLASSES:
            row = [r for r in scored if r["label"] == k]
            if not row:
                continue
            c = Counter(r["guess"] for r in row)
            w(f"| `{k}` | " + " | ".join(str(c.get(s, "")) for s in seen) + " |")
        w("")

    # Does the blind arm err in a direction? The confusion matrix looks like it
    # skews toward slower classes, which would have a mechanism -- the Dafny
    # idioms are costlier than the Python's, so an agent reading the Dafny
    # correctly can land above a label derived from the Python. Eyeballing a
    # matrix is not evidence, so it is tested, and at this n it does not hold.
    if scored:
        over = under = samer = 0
        for r in scored:
            if r["guess_correct"]:
                continue
            a, b = RANK.get(canon(r["guess"])), RANK.get(canon(r["label"]))
            if a is None or b is None:
                continue
            over += a > b
            under += a < b
            samer += a == b
        tot = over + under
        w("### Do the wrong guesses lean one way?\n")
        w(f"- overestimated (guessed a slower class): {over}")
        w(f"- underestimated: {under}")
        w(f"- wrong but same growth rank: {samer}")
        if tot:
            from math import comb
            pv = sum(comb(tot, i) for i in range(max(over, under), tot + 1)) / 2 ** tot
            w(f"- one-sided sign test on the {tot} directional errors: p = {pv:.3f}")
            w("")
            w("At this sample size that is not evidence of a lean, whatever the"
              if pv > 0.05 else "That is a lean, not noise:")
            w("matrix looks like. Recorded so the question can be re-asked when"
              if pv > 0.05 else "recorded with the mechanism above.")
            w("the run is larger." if pv > 0.05 else "")
        w("")

    w("## Where a passing proof disagrees with the label\n")
    w("A proof gives an UPPER bound, so the direction of a disagreement decides")
    w("what it means. Only a bound strictly tighter than the label contradicts")
    w("it -- an n log n program also satisfies steps <= c*n^2, so a looser bound")
    w("is consistent with the label and carries no news. An agent charging a seq")
    w("append flatly produces exactly that kind of loose bound.\n")
    dis = [r for r in rs if r["proved"] and r["label_match"] is False
           and not r["degenerate"]]
    deg = [r for r in rs if r["degenerate"]]
    if deg:
        w(f"**{len(deg)} bound(s) excluded as degenerate**: a constant bound on a")
        w("program that loops over its input, bought by folding the statement's")
        w("numeric cap into the constant. True, verifiable, and vacuous.\n")
        for r in deg:
            w(f"- {r['arm']} `{r['sid']}` (label `{r['label']}`): "
              f"`{r['bound_ensures']}`")
        w("")
    for kind, gloss in (
            ("tighter", "**refutes the label** -- provably cheaper than claimed"),
            ("same-rank", "same growth rank, different naming of the sizes"),
            ("looser", "consistent with the label; the proof is loose, not news")):
        g = [r for r in dis if r["direction"] == kind]
        w(f"### {kind}: {len(g)} -- {gloss}\n")
        if g:
            w("| arm | sid | label | proved | drift | ensures |")
            w("|---|---|---|---|---|---|")
            for r in g:
                w(f"| {r['arm']} | `{r['sid']}` | `{r['label']}` | "
                  f"`{r['bound_class']}` | {r['drift_kind'] or '-'} | "
                  f"`{r['bound_ensures']}` |")
        w("")

    w("## Gate failures\n")
    w("| gate | labeled | blind |")
    w("|---|---|---|")
    for g, nice in (("gate_verify", "did not verify"),
                    ("gate_no_assume", "used `assume`"),
                    ("gate_skeleton", "compiled control flow changed"),
                    ("gate_behaviour", "behaviour changed"),
                    ("gate_requires", "a `requires` excludes real inputs")):
        w(f"| {nice} | {sum(1 for r in L if r[g] is False)} "
          f"| {sum(1 for r in B if r[g] is False)} |")
    w("")

    w("## Difficulty: declared before the run vs measured\n")
    w("| difficulty_static | n | proved | mean dafny calls | mean difficulty_measured |")
    w("|---|---|---|---|---|")
    for d in sorted({r["difficulty_static"] for r in rs}):
        g = [r for r in rs if r["difficulty_static"] == d]
        dc = [r["dafny_calls"] for r in g if r["dafny_calls"] is not None]
        mean_dc = f"{sum(dc)/len(dc):.1f}" if dc else "-"
        mean_md = sum(r["difficulty_measured"] for r in g) / len(g)
        w(f"| {d} | {len(g)} | {sum(1 for r in g if r['proved'])} | "
          f"{mean_dc} | {mean_md:.1f} |")
    w("")

    leaks = [r for r in rs if r["leak_attempts"]]
    w("## Anti-cheat\n")
    w(f"- blind examples with a leak attempt: **{len([r for r in leaks if r['arm']=='blind'])}**")
    for r in leaks:
        w(f"  - `{r['sid']}` ({r['arm']}): {r['leak_attempts']} attempts")
    w("")
    return "\n".join(o) + "\n"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--run-id", required=True)
    a = ap.parse_args()
    rs = rows(a.run_id)
    rd = RUNS / a.run_id
    with (rd / "results.csv").open("w", newline="", encoding="utf-8") as fh:
        wr = csv.DictWriter(fh, fieldnames=FIELDS)
        wr.writeheader()
        wr.writerows(rs)
    (rd / "RESULTS.md").write_text(report(rs), encoding="utf-8")

    empty = [f for f in FIELDS
             if all(r.get(f) in (None, "", []) for r in rs)] if rs else FIELDS
    print(f"{len(rs)} rows -> {rd/'results.csv'}")
    print(f"report      -> {rd/'RESULTS.md'}")
    if empty:
        print("COLUMNS THAT NEVER POPULATED (a recorder defect, not a result):")
        for f in empty:
            print("  " + f)


if __name__ == "__main__":
    main()
