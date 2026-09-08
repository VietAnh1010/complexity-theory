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
from bound import CLASSES, same_class                             # noqa: E402

HERE = Path(__file__).resolve().parent
RUNS = HERE / "runs"

FIELDS = ["run_id", "arm", "sid", "problem_id", "label", "split", "model",
          "difficulty_static", "difficulty_measured", "drift", "drift_kind",
          "guess", "guess_correct", "verdict",
          "proved", "bound_class", "bound_shape", "bound_ensures",
          "label_match", "added_requires",
          "gate_verify", "gate_no_assume", "gate_skeleton", "gate_behaviour",
          "gate_requires", "requires_detail",
          "code_identical", "added_exec_lines", "assumes",
          "dafny_calls", "tool_calls", "wall_s", "output_tokens",
          "leak_attempts", "attempts", "agent_id", "notes"]


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
    L = [r for r in rs if r["arm"] == "labeled"]
    B = [r for r in rs if r["arm"] == "blind"]
    o = []
    w = o.append

    w("# Complexity-proving experiment\n")
    w(f"{len(rs)} runs: {len(L)} labeled, {len(B)} blind.\n")

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
    clean = [r for r in B if not r["leak_attempts"]]
    scored = [r for r in clean if r["guess"]]
    ok = sum(1 for r in scored if r["guess_correct"])
    w(f"- guessed on {len(scored)} of {len(B)} examples "
      f"({len(B) - len(clean)} excluded for a leak attempt)")
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

    w("## Where a passing proof disagrees with the label\n")
    w("Split by whether the TRANSLATION drifts from its Python. A proof is")
    w("about the Dafny; where the two differ in shape, a disagreement with the")
    w("label is a fact about this dataset's translation, not about BigOBench.\n")
    dis = [r for r in rs if r["proved"] and r["label_match"] is False]
    w(f"- disagreements on rows with NO drift signal: "
      f"**{sum(1 for r in dis if not r['drift'])}**")
    w(f"- disagreements on rows WITH a drift signal:  "
      f"**{sum(1 for r in dis if r['drift'])}**\n")
    if dis:
        w("| arm | sid | label | proved | drift | ensures |")
        w("|---|---|---|---|---|---|")
        for r in dis:
            w(f"| {r['arm']} | `{r['sid']}` | `{r['label']}` | "
              f"`{r['bound_class']}` | {r['drift_kind'] or '-'} | "
              f"`{r['bound_ensures']}` |")
    else:
        w("None.")
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
