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
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from bound import CLASSES, RANK, canon, direction, same_class     # noqa: E402
from common import SOLUTIONS                                      # noqa: E402
from features import (class_risk, drift as drift_now, split_file,  # noqa: E402
                      strip_comments)


def live_drift(sid, tasks_src):
    """Recompute drift with the CURRENT rule instead of reading the manifest.

    manifest.json is the pre-run record and is left alone -- it is what the
    selection was registered on. But `drift` is a derived feature, not an
    outcome, and its append rule was wrong when pilot1 was graded: it called
    `s := s + [x]` in a loop a class slower than Python's `list.append`, which
    a measurement then contradicted. Reading the stale value would keep
    publishing the wrong tag. `drift_stale` marks the rows where the two
    disagree, because an agent that saw the old flag may have charged the
    append |s| and reached a bound that is an artifact of the charge.
    """
    f = next(Path(SOLUTIONS).rglob(f"{sid}.dfy"), None)
    if f is None:
        return None
    body = strip_comments(split_file(f.read_text(encoding="utf-8"))[1])
    return drift_now(body, tasks_src.get(sid, ""))

HERE = Path(__file__).resolve().parent
RUNS = HERE / "runs"

FIELDS = ["run_id", "arm", "sid", "problem_id", "label", "split", "model",
          "difficulty_static", "difficulty_measured", "drift", "drift_kind",
          "drift_stale", "guide", "class_risk",
          "guess", "guess_correct", "verdict",
          "proved", "bound_class", "bound_shape", "bound_ensures",
          "label_match", "direction", "degenerate", "stub", "declined",
          "added_requires",
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


_TASKS_CACHE = {}


def _tasks_src():
    if not _TASKS_CACHE:
        from common import DATA
        for line in (DATA / "tasks.jsonl").read_text(encoding="utf-8").splitlines():
            r = json.loads(line)
            _TASKS_CACHE[r["solution_id"]] = (r.get("python_source")
                                              or r.get("solution_code") or "")
    return _TASKS_CACHE


def guide_v2_sids(run_id):
    """Which examples ran under the corrected guide.

    The append charge changed mid-run, so a row's guide version is part of its
    provenance. `drift_stale` catches a stale charge that reached the BOUND;
    this catches one that reached the NOTES, which no structural check can see
    -- blind/1733_64 argues a cubic true cost "charged real cost |s| per
    GUIDE.md", reasoning straight from the withdrawn rule.
    """
    f = RUNS / run_id / "guide_v2_sids.json"
    if not f.exists():
        return set()
    return set(json.loads(f.read_text(encoding="utf-8")).get("sids") or [])


def row_class_risk(sid):
    f = next(Path(SOLUTIONS).rglob(f"{sid}.dfy"), None)
    if f is None:
        return {}
    return class_risk(strip_comments(split_file(f.read_text(encoding="utf-8"))[1]))


def rows(run_id):
    graded, traj = load(run_id)
    v2 = guide_v2_sids(run_id)
    man = {e["sid"]: e for e in
           json.loads((HERE / "manifest.json").read_text())["examples"]}
    out = []
    for g in graded:
        res = g.get("result") or {}
        t, ag = combine(traj.get((g["arm"], g["sid"]), []))
        proved = bool(g.get("gate_all"))
        dr_manifest = (man.get(g["sid"], {}) or {}).get("drift", {})
        dr = live_drift(g["sid"], _tasks_src()) or dr_manifest
        stale = bool(dr_manifest.get("drift_slower")) and not bool(dr.get("drift_slower"))
        beh = g.get("gate_behaviour") or {}
        r = {
            "run_id": g["run_id"], "arm": g["arm"], "sid": g["sid"],
            "problem_id": g["problem_id"], "label": g["label"],
            "split": g["split"], "model": (ag or {}).get("model"),
            "difficulty_static": g["difficulty_static"],
            "drift": bool(dr.get("drift_slower") or dr.get("drift_sort")),
            "drift_stale": stale,
            "guide": "v2" if g["sid"] in v2 else "v1",
            "class_risk": bool(row_class_risk(g["sid"]).get("class_risk")),
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
            #
            # "untouched" alone stopped being the discriminator when the guide
            # started telling agents to give up rather than invent a charge for
            # `Join`. That produces a REASONED give-up whose file is also
            # untouched -- the agent read the method, priced every other part,
            # and declined the one term it could not price. Excluding it as a
            # rate-limit casualty would hide the obstruction the run exists to
            # find. `notes` is what separates them: a casualty dies before
            # writing any, a reasoned give-up says which obligation stopped it.
            "stub": (not g.get("touched") and not g.get("bound_ensures")
                     and not (res.get("notes") or "").strip()),
            "declined": bool(not g.get("touched") and not g.get("bound_ensures")
                             and (res.get("notes") or "").strip()),
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
    safe = [r for r in scored if not r["class_risk"]]
    risky = [r for r in scored if r["class_risk"]]
    if risky:
        ok_s = sum(1 for r in safe if r["guess_correct"])
        ok_r = sum(1 for r in risky if r["guess_correct"])
        w(f"- on rows the translation cannot have re-classed: "
          f"**{ok_s}/{len(safe)}**"
          + (f" = {100*ok_s/len(safe):.0f}%" if safe else ""))
        w(f"- on rows containing a class-changing construct: "
          f"**{ok_r}/{len(risky)}**"
          + (f" = {100*ok_r/len(risky):.0f}%" if risky else ""))
    w("")
    if risky:
        w("The blind agent reads the **Dafny**; the label was measured on the "
          "**Python**. A seq functional update in a loop is O(1) in CPython and "
          "a full copy in Dafny, and a `set` built in a loop is quadratic in "
          "Dafny -- both measured. On a row containing one, the two programs "
          "can sit in different classes, and an agent that reads its input "
          "correctly is then scored wrong against the label.\n")
        w("`1039_15` is the established case, not a hypothesis: the blind agent "
          "guessed `O(n**2)` before proving, PROVED `O(n**2)`, and wrote that "
          "the Python is O(n log n) because array assignment is O(1) there. It "
          "is scored incorrect against an `O(nlogn)` label. Its labeled twin "
          "reached the same quadratic independently.\n")
        w("The split above is reported, not corrected: the pooled number is "
          "still the honest answer to \"did it name the label\". It is the "
          "wrong denominator for \"can it read a program\".\n")
        w("| sid | label | guess | scored |")
        w("|---|---|---|---|")
        for r in sorted(risky, key=lambda r: r["sid"]):
            w(f"| `{r['sid']}` | `{r['label']}` | `{r['guess']}` | "
              f"{'correct' if r['guess_correct'] else 'incorrect'} |")
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

    w("## Claimed refutations, and which of them the proof carries\n")
    w("A ghost step counter proves an UPPER bound. It can refute a label only")
    w("by proving something strictly TIGHTER -- the program is faster than")
    w("claimed. It can never show a program is SLOWER than claimed: that needs")
    w("a lower bound, and this method cannot produce one. An agent that charges")
    w("a string concat honestly, lands on n^2 against an O(n) label, and writes")
    w("`refutes` has proved a bound the label already satisfies.\n")
    w("The agent's own verdict is recorded as its belief. The direction of the")
    w("bound decides what was established.\n")
    good = [r for r in scorable if r["verdict"] == "refutes"
            and r["direction"] == "tighter"]
    weak = [r for r in scorable if r["verdict"] == "refutes"
            and r["direction"] in ("looser", "same-rank")]
    w(f"- claimed `refutes`, proof is tighter -- **established**: {len(good)}")
    for r in good:
        w(f"  - {r['arm']} `{r['sid']}` `{r['label']}` -> `{r['bound_class']}`")
    w(f"- claimed `refutes`, proof is only an upper bound -- **not established**: "
      f"{len(weak)}")
    for r in weak:
        w(f"  - {r['arm']} `{r['sid']}` `{r['label']}` -> `{r['bound_class']}` "
          f"({r['direction']})")
    w("")
    w("The mechanism those agents describe -- a string or seq concat inside a")
    w("loop, genuinely linear in Dafny where CPython amortises it away -- may")
    w("well be right. It is not what their artifact proves.\n")

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

    # A `gave_up` stub with an untouched file is a rate-limit casualty, not a
    # verdict -- the same exclusion the proof rate uses. Nothing to re-cite.
    declined = [r for r in (L + B) if r.get("declined")]
    if declined:
        w("## Declined rather than guessed at a cost\n")
        w("The file is untouched and `notes` says why. These are NOT stubs: "
          "the agent read the method, priced the parts it could, and refused "
          "the one term the charging convention does not yet cover. They count "
          "as not-proved in the rate above, which is right -- no bound was "
          "produced -- but the reason is an obstruction in the convention, not "
          "a limit of the agent.\n")
        for r in sorted(declined, key=lambda r: (r["sid"], r["arm"])):
            w(f"- {r['arm']} `{r['sid']}` (label `{r['label']}`, guide "
              f"`{r['guide']}`)")
        w("")
        if any(r["guide"] == "v1" for r in declined):
            w("A `v1` decline states its obstacle in prose written under the "
              "superseded append charge, so the REASON it gives may be an "
              "artifact even though the decline itself stands. blind "
              "`1733_64` is the clear case: it argues a cubic true cost from "
              "appends \"charged real cost |s| per GUIDE.md\". Re-run those "
              "under v2 before quoting their analysis.\n")

    stale = [r for r in (L + B)
             if r.get("drift_stale") and r.get("bound_class")
             and r.get("bound_class") != "unclassified"]
    if stale:
        w("## Verdicts computed under a superseded charge\n")
        w("`s := s + [x]` was charged O(|s|) when these ran. It is O(1) "
          "amortised -- the Python backend defers the concatenation, and only "
          "an element read of the accumulator inside the same loop forces the "
          "flatten that makes the pattern quadratic. Measured; "
          "`bigodafny/COMPLEXITY.md` carries the numbers.\n")
        w("An overcharge does not produce a false proof -- the bound still "
          "holds. It produces a false DISAGREEMENT: a linear row charged this "
          "way lands on a quadratic bound and reads as contradicting an O(n) "
          "label. So each bound below is sound and each row needs re-proving, "
          "not re-reading. The rows to re-prove first are those whose "
          "`direction` is not `equal`: there the overcharge is what put the "
          "proof in a different class from the label.\n")
        w("| arm | sid | label | proved | direction | verdict |")
        w("|---|---|---|---|---|---|")
        for r in sorted(stale, key=lambda r: (r["sid"], r["arm"])):
            w(f"| {r['arm']} | `{r['sid']}` | `{r['label']}` | "
              f"`{r['bound_class']}` | {r.get('direction') or '-'} | "
              f"{r.get('verdict') or '-'} |")
        w("")
        w(f"{len(stale)} of {len(L) + len(B)} graded runs. The manifest keeps "
          "the flag it was registered with; this table is computed from the "
          "current rule.\n")

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
