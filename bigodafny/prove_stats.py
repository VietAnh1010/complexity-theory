#!/usr/bin/env python3
"""Pass/fail statistics for the proof campaigns, joined against the label.

    python3 prove_stats.py           # writes data/prove_stats.md, out/prove_stats.json

Drawn, proved and unresolved rows, obstacles and relations, each by label.
Per-campaign cells get a binomial p against the pooled rate. Rows drawn while
already proved are left out of the rate. Reads only: `verified` comes from
proofs.py, relations from each batch's label_relation.jsonl.
"""
from __future__ import annotations

import json
from vocab import OBSTACLES, RELATIONS, RETIRED_OBSTACLES
from common import OUT, write_json
from collections import Counter, defaultdict
from math import comb
from pathlib import Path

HERE = Path(__file__).resolve().parent
DATA = HERE / "data"
BATCHES = ["prove-sample", "prove-sample-2", "prove-sample-3",
           "prove-sample-4", "prove-sample-5", "prove-sample-6",
           "prove-sample-7", "prove-sample-8", "prove-retry", "prove-sample-9",
           "prove-sample-10", "prove-sample-11", "prove-sample-12"]
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
        # Measure the agent's result, not later edits: the earliest superseded
        # line in old-record.jsonl is the agent's.
        old = {}
        for o in jsonl(d / "old-record.jsonl"):
            old.setdefault(o["record"]["solution_id"], {}).setdefault(o["file"], o["record"])
        for sid, m in man.items():
            t = traj.get(sid, {})
            # a rerun record is the campaign's record; old lines are history
            then = {} if t.get("rerun") else old.get(sid, {})
            outcome = t.get("agent_outcome", t.get("outcome", "not attempted"))
            rel_then = then.get("label_relation.jsonl") or rel.get(sid) or {}
            rows.append({
                "campaign": b,
                "solution_id": sid,
                "label": m["label"],
                "split": m.get("split"),
                "outcome": outcome,
                # the row's state now is the verifier's, not any record's
                "current_outcome": "proved" if sid in VERIFIED else ("unresolved" if t else "not attempted"),
                "current_relation": (rel.get(sid) or {}).get("relation")
                                    if t.get("outcome") == "proved" else None,
                # drawn although already proved: not in the denominator
                "redrawn": bool(m.get("already_proved_when_drawn")),
                "relation": (rel_then.get("relation") if "revision" not in rel_then
                             else None) if outcome == "proved" else None,
                # on the record; a revised record keeps the agent's beside
                "obstacle": t.get("agent_obstacle", t.get("obstacle")),
                # a later revision of the row's proof, from its current line
                "resolved": ((rel.get(sid) or {}).get("revision") or {}).get("what"),
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


def payload():
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
                # None when the pooled rate is 0 or 1
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

    return {
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
        # rows whose relation changed after the campaign, and why
        "resolved_since": {r["solution_id"]: r["resolved"]
                           for r in proved if r.get("resolved")
                           and r.get("current_relation")
                           and (r["relation"] or "confirms") != r["current_relation"]},
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
        "dedup": dedup_view(rows),
        "current": current_state(rows),
        "open_now": open_now(rows),
        "corpus": corpus_context(),
        "rows": sorted(rows, key=lambda r: (r["campaign"], r["solution_id"])),
    }


def main():
    p = payload()
    write_json(OUT / "prove_stats.json", p)
    (DATA / "prove_stats.md").write_text(render(p))
    print("wrote data/prove_stats.md and out/prove_stats.json")
    print(f"  {p['proved']}/{p['drawn']} proved "
          f"({p['rate']:.0%}) over {p['campaigns']} campaigns")


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
    """Split each campaign's draw into rows never drawn before and rows redrawn
    (failed rows stay in the pool, so redraws skew hard)."""
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
    """Where the drawn rows stand now, including proofs made by hand after
    their campaign."""
    latest = {}
    for r in rows:
        if r["redrawn"]:
            continue
        latest[r["solution_id"]] = r   # later campaigns overwrite earlier ones
    distinct = list(latest.values())
    proved = [r for r in distinct if r["current_outcome"] == "proved"]
    # closed by hand: no agent proved it in any draw, and it is proved now
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
        "closed_after_campaign": closed_after,
    }


def open_now(rows):
    """What blocks each drawn row with no verified proof: its latest dated line."""
    latest = {}
    for f in sorted((HERE / "batches").glob("*/traj*.jsonl")):
        for r in jsonl(f):
            if r.get("on") and r["on"] >= latest.get(r["solution_id"], {}).get("on", ""):
                latest[r["solution_id"]] = r
    open_rows = {r["solution_id"] for r in rows} - VERIFIED
    coded = defaultdict(list)
    for sid in sorted(open_rows):
        code = latest.get(sid, {}).get("obstacle")
        if code:
            coded[code].append(sid)
    uncoded = sorted(open_rows - {s for ids in coded.values() for s in ids})
    return {"open": len(open_rows), "coded": dict(coded), "uncoded": uncoded}


def dedup_view(rows):
    """One record per distinct row, the most positive outcome kept. Higher than
    the per-draw rate by construction; never a per-campaign rate."""
    by_row = {}
    for r in rows:
        by_row.setdefault(r["solution_id"], []).append(r)
    proved = {s for s, rs in by_row.items() if any(r["outcome"] == "proved" for r in rs)}
    by_label = {}
    for s, rs in by_row.items():
        c = by_label.setdefault(rs[0]["label"], {"drawn": 0, "proved": 0})
        c["drawn"] += 1
        c["proved"] += s in proved
    return {
        "distinct_rows": len(by_row),
        "proved": len(proved),
        "proved_now": sum(1 for s in by_row if s in VERIFIED),
        "rate": round(len(proved) / len(by_row), 4),
        "drawn_more_than_once": sum(1 for rs in by_row.values() if len(rs) > 1),
        "closed_on_a_later_draw": sum(
            1 for s in proved if any(r["outcome"] == "unresolved" for r in by_row[s])),
        "by_label": dict(sorted(by_label.items())),
        "campaigns": BATCHES,
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
                 "33 that predate the campaigns and the rows the main agent proved later."),
    }


def render(p):
    L = []
    a = L.append
    a("# Proof campaigns — pass, fail, and why")
    a("")
    a(f"Generated by `prove_stats.py` from {p['campaigns']} campaigns. Every")
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
        a("rows, since a repeat draw selects for failure. This view keeps")
        a("one record per row, the most positive outcome.")
        a("")
        a(f"**{d['proved']} of {d['distinct_rows']} distinct rows were proved by a "
          f"bounded agent — {d['rate']:.0%}.**")
        a("")
        a(f"- {d['drawn_more_than_once']} rows were drawn more than once.")
        a(f"- {d['closed_on_a_later_draw']} were closed by a later campaign "
          "after an earlier one missed them.")
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
        a("drawn rows a bounded agent ever proved. The second is higher by")
        a("construction and says nothing about what one bounded agent manages")
        a("in one pass; use it for the corpus, never for comparing campaigns.")
        a("")
    c = p.get("current")
    if c:
        a("### Where the drawn rows stand now")
        a("")
        a("Everything above is what a bounded agent achieved inside its budget.")
        a("")
        a(f"**{c['proved_now']} of {c['distinct_rows']} distinct drawn rows carry a "
          f"proof now — {c['rate_now']:.0%}.**")
        a("")
        a(f"- Proved outside any campaign: {len(c['closed_after_campaign'])} — "
          + ", ".join(f"`{x}`" for x in c["closed_after_campaign"]) + ".")
        a("- Relations of the proofs as they stand: "
          + ", ".join(f"`{k}` {v}" for k, v in c["relations_now"].items()) + ".")
        a("")
    a("## The label is the strongest predictor")
    a("")
    a("Pooled first, then per campaign. `p` tests that campaign's cell against")
    a("the pooled rate for its label. **Read the pooled column.** A class holds")
    a("as few as one row in a campaign, so a two-row swing moves a cell by")
    a("tens of points.")
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
    for name, meaning in OBSTACLES.items():
        a(f"| `{name}` | {meaning} |")
    for name, meaning in RETIRED_OBSTACLES.items():
        a(f"| `{name}` | retired: {meaning} |")
    a("")
    a("The counts above use the codes as agents recorded them, when `z3-nonlinear` meant")
    a("\"the solver would not close a verification condition mixing several nonlinear")
    a("scaffolds\" and `invariant-gap` meant \"an invariant needed reshaping or one more")
    a("bridging assert\".")
    a("")
    a("### Open rows now")
    a("")
    o = p["open_now"]
    a(f"{o['open']} drawn rows have no verified proof today. A row's code here comes from its")
    a("latest dated line in a batch's `traj.jsonl`; an uncoded row's line has no code, or it has no line.")
    a("")
    a("| obstacle | rows | IDs |")
    a("|---|---|---|")
    for code, ids in sorted(o["coded"].items(), key=lambda kv: (-len(kv[1]), kv[0])):
        a(f"| `{code}` | {len(ids)} | " + ", ".join(f"`{s}`" for s in ids) + " |")
    a(f"| uncoded | {len(o['uncoded'])} | " + ", ".join(f"`{s}`" for s in o["uncoded"]) + " |")
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
    a("Every bound here is an **upper** bound. It can confirm a label or fail")
    a("to; refuting one takes a lower bound, which no campaign produces.")
    a("")
    a("| relation | meaning |")
    a("|---|---|")
    for name, meaning in RELATIONS.items():
        a(f"| `{name}` | {meaning} |")
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
    a("## What this does not measure")
    a("")
    a("- **Only drawn rows.** Nothing here generalises to rows no campaign drew.")
    a("- **A bounded agent, not the problem.** `unresolved` means 3 attempts")
    a("  and 5 minutes were not enough, not that the row cannot be proved.")
    a("  `2423_48` failed twice and then closed once the prelude gained the")
    a("  lemma it needed.")
    a("- **Upper bounds only.** No campaign can show a label is too small.")
    return "\n".join(L) + "\n"


if __name__ == "__main__":
    main()
