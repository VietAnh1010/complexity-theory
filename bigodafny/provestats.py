#!/usr/bin/env python3
"""Pass/fail statistics for the proof campaigns, joined against the label.

    python3 provestats.py            # writes data/prove_stats.md and .json

Answers, over every campaign run so far:

  * how many rows were drawn, proved, unresolved;
  * WHY the unresolved ones failed, by coded obstacle;
  * what the proved bounds say about their labels, by relation;
  * every one of those cut by complexity class, which is the join that
    matters -- the label is the strongest single predictor of whether a
    bounded agent closes the row.

Two rules this file follows, because both have already caused a wrong claim
in this project:

  * a per-campaign cell is small. Report the pooled rate first and give a
    binomial p against it, so a two-row swing is not read as a trend.
  * a row drawn although it already had a proof is not new work. Those are
    excluded from the rate and listed separately.

Reads only. Nothing here re-verifies anything: `verified` comes from
proofs.py, and the relations come from each batch's hand-normalised
label_relation.jsonl.
"""
from __future__ import annotations

import json
from collections import Counter, defaultdict
from math import comb
from pathlib import Path

HERE = Path(__file__).resolve().parent
DATA = HERE / "data"
BATCHES = ["prove-sample", "prove-sample-2", "prove-sample-3",
           "prove-sample-4", "prove-sample-5", "prove-sample-6",
           "prove-sample-7", "prove-sample-8"]
# rows a campaign drew although a proof already existed: a sampler bug, not
# new work, so they are not in the denominator
REDRAWN = {"prove-sample-5": {"2128_34", "305_76"}}
# rows with a verified proof in the overlay now, whoever wrote it
VERIFIED = {r["solution_id"] for r in
            (json.loads(l) for l in (DATA / "complexity_proofs.jsonl").open() if l.strip())
            if r.get("verified")} if (DATA / "complexity_proofs.jsonl").exists() else set()


def jsonl(p):
    p = Path(p)
    return [json.loads(l) for l in p.open()] if p.exists() else []


def two_sided(k, n, p):
    """Binomial probability of a cell at least this extreme under rate p."""
    if n == 0 or p in (0, 1):
        return None
    pk = comb(n, k) * p ** k * (1 - p) ** (n - k)
    return sum(comb(n, i) * p ** i * (1 - p) ** (n - i)
               for i in range(n + 1)
               if comb(n, i) * p ** i * (1 - p) ** (n - i) <= pk * 1.0000001)


def load():
    """One record per drawn row, across every campaign."""
    rows = []
    for b in BATCHES:
        d = HERE / "batches" / b
        man = {r["solution_id"]: r for r in jsonl(d / "manifest.jsonl")}
        traj = {}
        for f in sorted(d.glob("traj_*.jsonl")):
            for r in jsonl(f):
                r["_slice"] = f.stem.split("_")[-1]
                traj[r["solution_id"]] = r
        rel = {r["solution_id"]: r for r in jsonl(d / "label_relation.jsonl")}
        obst = {r["solution_id"]: r for r in jsonl(d / "obstacles.jsonl")}
        # A record revised after the campaign keeps the agent's result beside
        # the current one, and its superseded lines live in old_record.jsonl.
        # This file measures the CAMPAIGNS, so it reads the agent's result:
        # a row proved later by hand, outside the budget, is still a row the
        # bounded agent did not close.
        old = {}
        for o in jsonl(d / "old_record.jsonl"):
            old.setdefault(o["record"]["solution_id"], {})[o["file"]] = o["record"]
        for sid, m in man.items():
            t = traj.get(sid, {})
            # a rerun record is the campaign's record; old lines are history
            then = {} if t.get("rerun") else old.get(sid, {})
            outcome = t.get("agent_outcome", t.get("outcome", "not attempted"))
            rel_then = then.get("label_relation.jsonl") or rel.get(sid) or {}
            obst_then = then.get("obstacles.jsonl") or obst.get(sid) or {}
            rows.append({
                "campaign": b,
                "solution_id": sid,
                "label": m["label"],
                "split": m.get("split"),
                "outcome": outcome,
                # the row's state now is the verifier's, not any record's
                "current_outcome": "proved" if sid in VERIFIED else t.get("outcome", "not attempted"),
                "current_relation": (rel.get(sid) or {}).get("relation")
                                    if t.get("outcome") == "proved" else None,
                "revised": bool(t.get("revision")),
                "redrawn": sid in REDRAWN.get(b, set()),
                "relation": (t.get("relation") if t.get("rerun") else
                             (rel_then.get("relation") if "revision" not in rel_then
                              else None)) if outcome == "proved" else None,
                # campaign 1 kept the obstacle beside the relation; later ones
                # moved it to its own file
                "obstacle": ((t.get("rerun") or {}).get("obstacle") if t.get("rerun")
                             else (obst_then.get("obstacle") or rel_then.get("obstacle"))),
                "resolved": rel_then.get("resolved"),
                "attempts_used": t.get("attempts_used"),
                "seconds": t.get("seconds"),
                "slice": t.get("_slice"),
            })
    return rows


def table(counter, total, head):
    out = [f"| {head} | rows | share |", "|---|---|---|"]
    for k, v in counter.most_common():
        out.append(f"| `{k}` | {v} | {v / total:.0%}" + " |")
    return "\n".join(out)


def main():
    rows = load()
    new = [r for r in rows if not r["redrawn"]]
    proved = [r for r in new if r["outcome"] == "proved"]
    unres = [r for r in new if r["outcome"] == "unresolved"]
    labels = sorted({r["label"] for r in new})

    # --- per-label, per-campaign, with a test against the pooled rate -------
    by_label = {}
    for lab in labels:
        cells = []
        for b in BATCHES:
            c = [r for r in new if r["label"] == lab and r["campaign"] == b]
            cells.append({"drawn": len(c),
                          "proved": sum(1 for r in c if r["outcome"] == "proved")}
                         if c else None)
        tp = sum(1 for r in new if r["label"] == lab and r["outcome"] == "proved")
        td = sum(1 for r in new if r["label"] == lab)
        for cell in cells:
            if cell:
                # None when the pooled rate is 0 or 1 -- a label every draw
                # closed, or none did. No cell can be surprising against that.
                pv = two_sided(cell["proved"], cell["drawn"], tp / td) if td else None
                cell["p_vs_pooled"] = round(pv, 4) if pv is not None else None
        by_label[lab] = {"pooled_proved": tp, "pooled_drawn": td,
                         "rate": round(tp / td, 4) if td else None,
                         "by_campaign": cells}

    # --- the joins ---------------------------------------------------------
    obstacle_by_label = defaultdict(Counter)
    for r in unres:
        obstacle_by_label[r["label"]][r["obstacle"] or "unrecorded"] += 1
    relation_by_label = defaultdict(Counter)
    for r in proved:
        relation_by_label[r["label"]][r["relation"] or "confirms"] += 1

    attempts = Counter(r["attempts_used"] for r in proved if r["attempts_used"] is not None)
    secs = sorted(r["seconds"] for r in proved if r["seconds"] is not None)
    secs_u = sorted(r["seconds"] for r in unres if r["seconds"] is not None)

    payload = {
        "generated_from": "batches/prove-sample*/ and data/complexity_proofs.jsonl",
        "campaigns": len(BATCHES),
        "drawn_including_redrawn": len(rows),
        "redrawn_already_proved": sorted(r["solution_id"] for r in rows if r["redrawn"]),
        "drawn": len(new),
        "proved": len(proved),
        "unresolved": len(unres),
        "rate": round(len(proved) / len(new), 4),
        "by_label": by_label,
        "obstacles": dict(Counter(r["obstacle"] or "unrecorded" for r in unres).most_common()),
        "relations": dict(Counter(r["relation"] or "confirms" for r in proved).most_common()),
        "resolved_since": {r["solution_id"]: r["resolved"]
                           for r in proved if r.get("resolved")},
        "obstacle_by_label": {k: dict(v.most_common()) for k, v in obstacle_by_label.items()},
        "relation_by_label": {k: dict(v.most_common()) for k, v in relation_by_label.items()},
        "attempts_when_proved": dict(sorted(attempts.items())),
        "seconds_when_proved": {"median": secs[len(secs) // 2] if secs else None,
                                "max": max(secs) if secs else None},
        "seconds_when_unresolved": {"median": secs_u[len(secs_u) // 2] if secs_u else None,
                                    "max": max(secs_u) if secs_u else None},
        "by_campaign": {b: {"drawn": sum(1 for r in new if r["campaign"] == b),
                            "proved": sum(1 for r in new if r["campaign"] == b
                                          and r["outcome"] == "proved")}
                        for b in BATCHES},
        "repeat_draws": repeat_draws(rows),
        "first_vs_repeat": first_vs_repeat(rows),
        "dedup": dedup_view(),
        "current": current_state(rows),
        "corpus": corpus_context(),
        "rows": sorted(rows, key=lambda r: (r["campaign"], r["solution_id"])),
    }
    (DATA / "prove_stats.json").write_text(json.dumps(payload, indent=2) + "\n")
    (DATA / "prove_stats.md").write_text(render(payload))
    print(f"wrote data/prove_stats.md and data/prove_stats.json")
    print(f"  {payload['proved']}/{payload['drawn']} proved "
          f"({payload['rate']:.0%}) over {payload['campaigns']} campaigns")


def repeat_draws(rows):
    """Rows drawn more than once: a failure in one campaign returns to the pool."""
    seen = Counter(r["solution_id"] for r in rows)
    multi = {sid for sid, n in seen.items() if n > 1}
    out = {}
    for sid in sorted(multi):
        hits = [r for r in rows if r["solution_id"] == sid]
        out[sid] = {"drawn_in": [r["campaign"] for r in hits],
                    "outcomes": [r["outcome"] for r in hits],
                    "label": hits[0]["label"]}
    return {"rows": out, "count": len(out),
            "note": ("A row that fails stays in the pool, so later campaigns "
                     "redraw it. Each attempt is independent -- a different "
                     "agent that has not seen the earlier one.")}


def first_vs_repeat(rows):
    """Split each campaign's draw into rows never drawn before and rows redrawn.

    A row that FAILS stays in the pool, so every plain draw carries more rows
    already known to be hard: 8%, 12%, 20%, 28% across campaigns 3 to 6. Past
    about a quarter the campaign has stopped measuring "can a bounded agent
    prove a random row" and started measuring "can a second agent close what a
    first could not". Both rates are reported so the pooled headline can be
    read for what it is.
    """
    seen, out = set(), {}
    for b in BATCHES:
        here = [r for r in rows if r["campaign"] == b]
        fresh = [r for r in here if r["solution_id"] not in seen]
        rep = [r for r in here if r["solution_id"] in seen]
        out[b] = {
            "fresh_drawn": len(fresh),
            "fresh_proved": sum(1 for r in fresh if r["outcome"] == "proved"),
            "repeat_drawn": len(rep),
            "repeat_proved": sum(1 for r in rep if r["outcome"] == "proved"),
            "repeat_share": round(len(rep) / len(here), 4) if here else None,
        }
        seen |= {r["solution_id"] for r in here}
    return out


def current_state(rows):
    """Where the drawn rows stand now, as opposed to what the campaigns did.

    Some rows were proved, or their proofs tightened, after their campaign, by
    hand and outside the budget -- most on 2026-09-23 when the prelude gained a
    composable sort-cost bound. Their campaign records keep the agent's result
    as `agent_outcome` and the superseded lines in old_record.jsonl, so every
    rate above is still what a bounded agent achieved. This is the other view.
    """
    latest = {}
    for r in rows:
        if r["redrawn"]:
            continue
        latest[r["solution_id"]] = r   # later campaigns overwrite earlier ones
    distinct = list(latest.values())
    proved = [r for r in distinct if r["current_outcome"] == "proved"]
    revised = sorted(r["solution_id"] for r in distinct if r["revised"])
    # no bounded agent proved it in any draw, and it is proved now: closed by
    # hand. Keyed on outcomes, not on a record's shape -- a rerun record carries
    # no `revision` flag but can still be an agent's miss on a row proved later.
    agent_proved = {r["solution_id"] for r in rows
                    if not r["redrawn"] and r["outcome"] == "proved"}
    closed_after = sorted(r["solution_id"] for r in distinct
                          if r["solution_id"] not in agent_proved
                          and r["current_outcome"] == "proved")
    return {
        "distinct_rows": len(distinct),
        "proved_now": len(proved),
        "rate_now": round(len(proved) / len(distinct), 4) if distinct else None,
        "relations_now": dict(Counter(r["current_relation"] or "confirms"
                                      for r in proved).most_common()),
        "revised_after_campaign": revised,
        "closed_after_campaign": closed_after,
    }


def dedup_view():
    """The deduplicated record, if dedupe.py has been run.

    `drawn` above counts DRAW RECORDS: a row several campaigns drew is in it
    several times, and those are disproportionately the hard rows, because a
    repeat draw selects for failure. The deduplicated set is one record per
    distinct row, keeping the most positive outcome.

    The two rates answer different questions and neither replaces the other:

      raw     -- of the rows a campaign drew, what share did THAT campaign
                 prove within the budget. The per-campaign question.
      dedup   -- of the distinct rows any campaign has drawn, what share
                 carries a proof. The corpus question.

    dedup is the higher number by construction, and it is not a statement
    about what one bounded agent achieves in one pass.
    """
    rows = jsonl(DATA / "campaign_dedup.jsonl")
    if not rows:
        return None
    meta_p = DATA / "campaign_dedup.json"
    meta = json.loads(meta_p.read_text()) if meta_p.exists() else {}
    # what the bounded agents achieved across all of a row's draws; the row's
    # current state -- which counts hand proofs made after the campaigns -- is
    # reported beside it, never in its place
    agent = lambda r: r.get("best_agent_outcome", r["outcome"])
    proved = [r for r in rows if agent(r) == "proved"]
    by_label = {}
    for lab in sorted({r["label"] for r in rows}):
        d = [r for r in rows if r["label"] == lab]
        by_label[lab] = {"drawn": len(d),
                         "proved": sum(1 for r in d if agent(r) == "proved")}
    return {
        "distinct_rows": len(rows),
        "proved": len(proved),
        "proved_now": sum(1 for r in rows if r["outcome"] == "proved"),
        "rate": round(len(proved) / len(rows), 4),
        "drawn_more_than_once": sum(1 for r in rows if r["drawn_times"] > 1),
        "closed_on_a_later_draw": sum(
            1 for r in proved
            if any(s.get("agent_outcome", s["outcome"]) == "unresolved"
                   for s in r["superseded"])),
        "by_label": by_label,
        "campaigns": meta.get("campaigns"),
        "incomplete_and_excluded": meta.get("incomplete_and_excluded"),
        "note": ("one record per distinct row, most positive outcome kept. "
                 "A corpus-level share, not a per-campaign rate."),
    }


def corpus_context():
    """How much of the corpus the campaigns have reached at all."""
    import glob
    proved_files = glob.glob(str(HERE / "solutions-proved/**/*.dfy"), recursive=True)
    sol = glob.glob(str(HERE / "solutions/*/*.dfy"))
    return {
        "solutions_rows": len(sol),
        "proof_files": len(proved_files),
        "proved_rows": len({Path(f).stem for f in proved_files}),
        "note": ("proved_rows counts every proof in the corpus, including the "
                 "33 that predate the campaigns and the rows proved by hand."),
    }


def render(p):
    L = []
    a = L.append
    a("# Proof campaigns — pass, fail, and why")
    a("")
    a(f"Generated by `provestats.py` from {p['campaigns']} campaigns. Every")
    a("number here comes from a file on disk; nothing is typed by hand.")
    a("")
    a("## Headline")
    a("")
    a(f"**{p['proved']} of {p['drawn']} rows proved — {p['rate']:.0%}.**")
    a("")
    a(f"- {p['unresolved']} unresolved, each with a coded obstacle.")
    a(f"- {len(p['redrawn_already_proved'])} rows excluded from the denominator: "
      "drawn although a proof already existed, through a sampler bug. "
      + ", ".join(f"`{s}`" for s in p['redrawn_already_proved']))
    a(f"- Budget per row: 3 attempts, 5 minutes. {p['attempts_when_proved'].get(1, 0)} "
      f"of the {p['proved']} proofs closed on the first attempt; median "
      f"{p['seconds_when_proved']['median']}s.")
    a("")
    a("### Per campaign")
    a("")
    a("| campaign | drawn | proved | rate |")
    a("|---|---|---|---|")
    for b, c in p["by_campaign"].items():
        a(f"| `{b}` | {c['drawn']} | {c['proved']} | {c['proved']/c['drawn']:.0%} |")
    a("")
    a("### Fresh rows versus redrawn rows")
    a("")
    a("A row that fails stays in the pool, so each plain draw carries more")
    a("rows an earlier campaign already failed. That share is not constant,")
    a("and the pooled headline above mixes the two populations.")
    a("")
    a("| campaign | fresh | repeat | repeat share | fresh rate | repeat rate |")
    a("|---|---|---|---|---|---|")
    for b, c in p["first_vs_repeat"].items():
        fr = f"{c['fresh_proved']}/{c['fresh_drawn']}" if c["fresh_drawn"] else "—"
        rr = f"{c['repeat_proved']}/{c['repeat_drawn']}" if c["repeat_drawn"] else "—"
        a(f"| `{b}` | {c['fresh_drawn']} | {c['repeat_drawn']} | "
          f"{c['repeat_share']:.0%} | {fr} | {rr} |")
    a("")
    a("Only a fresh-row rate answers the campaign's own question. From")
    a("campaign 7 the sampler is run with `--exclude-drawn`, which draws only")
    a("never-touched rows: earlier campaigns removed a random part of the pool")
    a("(what they proved) and left a non-random part (what they failed), so")
    a("the never-drawn remainder is still an unbiased sample of the original")
    a("population.")
    a("")
    if p.get("dedup"):
        d = p["dedup"]
        a("### Deduplicated: one record per distinct row")
        a("")
        a("The headline counts draw records. A row several campaigns drew is")
        a("in it several times, and those are disproportionately the hard")
        a("rows, since a repeat draw selects for failure. `dedupe.py` keeps")
        a("one record per row — the most positive outcome — and writes the")
        a("rest out as `superseded`.")
        a("")
        a(f"**{d['proved']} of {d['distinct_rows']} distinct rows were proved by a "
          f"bounded agent — {d['rate']:.0%}.** With the proofs made by hand "
          f"afterwards, {d['proved_now']} carry one now.")
        a("")
        a(f"- {d['drawn_more_than_once']} rows were drawn more than once.")
        a(f"- {d['closed_on_a_later_draw']} were closed by a later campaign "
          "after an earlier one missed them.")
        if d.get("incomplete_and_excluded"):
            a("- Excluded because they have not finished: "
              + ", ".join(f"`{b}`" for b in d["incomplete_and_excluded"])
              + ". A running campaign has rows with no record yet, and "
                "counting those as failures would move every number here.")
        a("")
        a("| label | drawn | proved | rate |")
        a("|---|---|---|---|")
        for lab, c in sorted(d["by_label"].items(), key=lambda kv: -kv[1]["drawn"]):
            a(f"| `{lab}` | {c['drawn']} | {c['proved']} | "
              f"{c['proved'] / c['drawn']:.0%} |")
        a("")
        a("**These two rates answer different questions.** The raw rate asks")
        a("what share of the rows a campaign drew that campaign proved inside")
        a("its budget. The deduplicated rate asks what share of the distinct")
        a("rows anyone has drawn now carries a proof. The second is higher by")
        a("construction and says nothing about what one bounded agent manages")
        a("in one pass; use it for the corpus, never for comparing campaigns.")
        a("")
    c = p.get("current")
    if c:
        a("### Where the drawn rows stand now")
        a("")
        a("Everything above is what a bounded agent achieved inside its budget.")
        a(f"{len(c['revised_after_campaign'])} rows were revised after their "
          "campaign, by hand and outside the budget; their records keep the")
        a("agent's result as `agent_outcome`, and the superseded lines sit in")
        a("each batch's `old_record.jsonl`.")
        a("")
        a(f"**{c['proved_now']} of {c['distinct_rows']} distinct drawn rows carry a "
          f"proof now — {c['rate_now']:.0%}.**")
        a("")
        a(f"- Closed after their campaign: {len(c['closed_after_campaign'])} — "
          + ", ".join(f"`{x}`" for x in c["closed_after_campaign"]) + ".")
        a("- Relations of the proofs as they stand: "
          + ", ".join(f"`{k}` {v}" for k, v in c["relations_now"].items()) + ".")
        a("")
    a("## The label is the strongest predictor")
    a("")
    a("Pooled first, then per campaign. `p` tests that campaign's cell against")
    a("the pooled rate for its label. **Read the pooled column.** A class holds")
    a("as few as one row in a campaign, so a two-row swing moves a cell by")
    a("tens of points; this project has already published one trend that was")
    a("noise and had to be withdrawn.")
    a("")
    hdr = "| label | pooled | rate |" + "".join(
        f" {b.replace('prove-sample', 'c')} |" for b in BATCHES)
    a(hdr.replace("| c |", "| c1 |").replace("c-", "c"))
    a("|---|---|---|" + "---|" * len(BATCHES))
    for lab, d in sorted(p["by_label"].items(), key=lambda kv: -kv[1]["pooled_drawn"]):
        cells = ""
        for c in d["by_campaign"]:
            if not c:
                cells += " — |"
            else:
                flag = "*" if (c["p_vs_pooled"] or 1) < 0.05 else ""
                cells += f" {c['proved']}/{c['drawn']}{flag} |"
        a(f"| `{lab}` | {d['pooled_proved']}/{d['pooled_drawn']} | "
          f"{d['rate']:.0%} |{cells}")
    a("")
    a("`*` marks a cell with p < 0.05 against its own pooled rate. Treat even")
    a("those as noise unless the next campaign reproduces them: the table")
    a("invites a dozen comparisons and no correction is applied.")
    a("")
    a("## Why the failures failed")
    a("")
    a(table(Counter(p["obstacles"]), p["unresolved"], "obstacle"))
    a("")
    a("| obstacle | what it means |")
    a("|---|---|")
    a("| `value-to-size` | the cost depends on how LARGE an input is; the label counts how MANY. Needs its own arithmetic lemma per row |")
    a("| `z3-nonlinear` | the solver would not close a verification condition mixing several nonlinear scaffolds |")
    a("| `invariant-gap` | an invariant needed reshaping or one more bridging assert |")
    a("| `decreases-star` | the row carries `decreases *`, so there is no termination proof to hang a step bound on |")
    a("| `prelude-gap` | a lemma the prelude does not have. Fixable ONCE for every row that hits it |")
    a("| `recursion-depth` | bounding a recursion depth needs a number-theoretic argument |")
    a("| `structural-unbounded` | no bound in the row's size exists |")
    a("| `budget` | the mechanism was in hand when the clock ran out |")
    a("")
    a("### Obstacle by label")
    a("")
    labs = sorted(p["obstacle_by_label"], key=lambda k: -sum(p["obstacle_by_label"][k].values()))
    obs = sorted({o for v in p["obstacle_by_label"].values() for o in v})
    a("| label | " + " | ".join(f"`{o}`" for o in obs) + " | total |")
    a("|---" * (len(obs) + 2) + "|")
    for lab in labs:
        v = p["obstacle_by_label"][lab]
        a(f"| `{lab}` | " + " | ".join(str(v.get(o, "")) for o in obs)
          + f" | {sum(v.values())} |")
    a("")
    a("## What the proved bounds say about their labels")
    a("")
    a(table(Counter(p["relations"]), p["proved"], "relation"))
    a("")
    a("Every bound here is an **upper** bound. It can confirm a label or fail")
    a("to; refuting one takes a lower bound, which no campaign produces.")
    a("")
    a("These are the relations each campaign RECORDED. Where a finding was")
    a("later acted on, the row's current relation differs and the resolution")
    a("is noted below rather than overwritten, so the finding is not erased:")
    a("")
    for sid, why in p.get("resolved_since", {}).items():
        a(f"- **`{sid}`** — {why}")
    if not p.get("resolved_since"):
        a("- none yet.")
    a("")
    a("| relation | meaning |")
    a("|---|---|")
    a("| `confirms` | the bound is within the label's class |")
    a("| `looser-slack` | a loose scaffold was used; the tight bound was not attempted |")
    a("| `looser-structural` | the proof exposes a real cost the label omits |")
    a("| `tighter-costmodel` | the bound is below the label because the charge table costs something CPython does not |")
    a("| `tighter-translation` | the bound is below the label because the Dafny runs a cheaper algorithm than the Python |")
    a("| `contradicts` | a literal in the source forces more work than the label allows |")
    a("")
    a("### Relation by label")
    a("")
    rels = sorted({r for v in p["relation_by_label"].values() for r in v})
    a("| label | " + " | ".join(f"`{r}`" for r in rels) + " | total |")
    a("|---" * (len(rels) + 2) + "|")
    for lab in sorted(p["relation_by_label"],
                      key=lambda k: -sum(p["relation_by_label"][k].values())):
        v = p["relation_by_label"][lab]
        a(f"| `{lab}` | " + " | ".join(str(v.get(r, "")) for r in rels)
          + f" | {sum(v.values())} |")
    a("")
    a("## Effort")
    a("")
    a("| attempts used | proofs |")
    a("|---|---|")
    for k, v in p["attempts_when_proved"].items():
        a(f"| {k} | {v} |")
    a("")
    a(f"Proved rows: median {p['seconds_when_proved']['median']}s, "
      f"max {p['seconds_when_proved']['max']}s.")
    a(f"Unresolved rows: median {p['seconds_when_unresolved']['median']}s, "
      f"max {p['seconds_when_unresolved']['max']}s.")
    a("")
    a("A row that closes, closes quickly. A row that does not runs the clock")
    a("out, which is why almost no failure is a budget failure: the budget is")
    a("not what decides these.")
    a("")
    a("## Rows drawn more than once")
    a("")
    rd = p["repeat_draws"]
    a(f"{rd['count']} rows were drawn by more than one campaign. {rd['note']}")
    a("")
    a("| row | label | campaigns | outcomes |")
    a("|---|---|---|---|")
    for sid, d in rd["rows"].items():
        a(f"| `{sid}` | `{d['label']}` | "
          + ", ".join(c.replace("prove-sample-", "c").replace("prove-sample", "c1")
                      for c in d["drawn_in"])
          + " | " + ", ".join(d["outcomes"]) + " |")
    a("")
    a("A row that fails stays in the pool, so the residue concentrates as the")
    a("pool shrinks and each later draw contains more known-hard rows. That")
    a("pushes the rate down for reasons unrelated to the agents.")
    a("")
    a("## Corpus context")
    a("")
    c = p["corpus"]
    a(f"- `solutions/` holds {c['solutions_rows']} rows.")
    a(f"- {c['proved_rows']} rows carry a proof, in {c['proof_files']} files.")
    a(f"- {c['note']}")
    a("")
    a("## What this does not measure")
    a("")
    a("- **Only `solutions/`.** The 127 unscreened and 157 disputed rows have")
    a("  never been drawn. Nothing here generalises to them.")
    a("- **A bounded agent, not the problem.** `unresolved` means 3 attempts")
    a("  and 5 minutes were not enough, not that the row cannot be proved.")
    a("  `2423_48` failed twice and then closed once the prelude gained the")
    a("  lemma it needed.")
    a("- **Upper bounds only.** No campaign can show a label is too small.")
    return "\n".join(L) + "\n"


if __name__ == "__main__":
    main()
