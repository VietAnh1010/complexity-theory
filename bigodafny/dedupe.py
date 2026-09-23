#!/usr/bin/env python3
"""Reduce the campaign record to one entry per row, so the campaigns partition.

    python3 dedupe.py            # writes data/campaign_dedup.jsonl

A row that FAILS stays in the pool, so later campaigns redraw it: 350 draw
records cover 311 distinct rows. Anything computed over the raw records counts
those 39 extra draws twice or more, and weights them towards the rows that are
hard -- exactly the rows a repeat draw selects for.

This pass keeps ONE record per row and writes the others out as `superseded`.

The keep rule, in order:

  1. a `proved` record beats an `unresolved` one. The row is provable within
     the budget; a campaign that missed it does not make it less so.
  2. among equals, the LATEST campaign wins. For two `proved` records that is
     also the proof that survived in `solutions-proved/` -- the later one
     replaced the file. For all-unresolved rows it is the attempt run under
     the configuration closest to the current one.

The two rules never disagree on the present data: no row was proved by one
campaign and then recorded unresolved by a later one. `check()` asserts that,
so the day it stops being true this script fails instead of silently choosing.

WHAT THIS IS FOR, AND WHAT IT IS NOT FOR

For: a corpus-level number. "Of the distinct rows any campaign has drawn, what
share carries a proof" is a question about the corpus, and the deduplicated
set answers it without double-counting.

NOT for: comparing campaigns to each other. Attributing a row to the campaign
that PROVED it credits the later campaign with a row an earlier one failed,
which flatters late campaigns and penalises early ones. Per-campaign rates
belong to the raw records, split fresh-versus-repeat -- `provestats.py` keeps
that table and this pass does not touch it.

Reads only. No trajectory is edited: a later judgement about recorded data
goes in its own file beside it, never into the record itself.
"""
from __future__ import annotations

import json
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
BATCHES = ["prove-sample", "prove-sample-2", "prove-sample-3", "prove-sample-4",
           "prove-sample-5", "prove-sample-6", "prove-sample-7"]
RANK = {"proved": 2, "unresolved": 1, "not attempted": 0}


def short(b):
    return "c1" if b == "prove-sample" else "c" + b.rsplit("-", 1)[1]


def jsonl(p):
    p = Path(p)
    return [json.loads(l) for l in p.open() if l.strip()] if p.exists() else []


def complete(b):
    """True when every row this campaign drew has a trajectory line.

    A campaign still running has rows with no record yet. Folding it in would
    count those as failures and move every pooled number it touches, so an
    incomplete campaign is left out and named.
    """
    d = HERE / "batches" / b
    man = {r["solution_id"] for r in jsonl(d / "manifest.jsonl")}
    if not man:
        return False
    seen = set()
    for f in sorted(d.glob("traj_*.jsonl")):
        seen |= {r["solution_id"] for r in jsonl(f)}
    return man <= seen


def draws(batches):
    """Every (row, campaign) pair any campaign recorded, in campaign order."""
    out = []
    for b in batches:
        d = HERE / "batches" / b
        traj, rel = {}, {r["solution_id"]: r for r in jsonl(d / "label_relation.jsonl")}
        obst = {r["solution_id"]: r for r in jsonl(d / "obstacles.jsonl")}
        for f in sorted(d.glob("traj_*.jsonl")):
            for r in jsonl(f):
                r["_slice"] = f.stem.split("_", 1)[1]
                traj[r["solution_id"]] = r
        for m in jsonl(d / "manifest.jsonl"):
            sid = m["solution_id"]
            t = traj.get(sid, {})
            out.append({
                "solution_id": sid,
                "label": m["label"],
                "campaign": b,
                "slice": t.get("_slice"),
                "outcome": t.get("outcome", "not attempted"),
                "bound": t.get("bound"),
                # the hand-normalised relation where one exists; the agent's
                # otherwise. Never the other way round.
                "relation": (rel.get(sid) or t).get("relation"),
                "obstacle": ((obst.get(sid) or {}).get("obstacle")
                             or (rel.get(sid) or {}).get("obstacle")),
                "attempts_used": t.get("attempts_used"),
                "seconds": t.get("seconds"),
                "reads": len(t.get("reads") or []) or None,
            })
    return out


def check(by_row):
    """Fail loudly if the two keep rules could disagree."""
    bad = []
    for sid, rs in by_row.items():
        outs = [r["outcome"] for r in rs]
        if "proved" in outs and outs[outs.index("proved") + 1:].count("unresolved"):
            bad.append((sid, outs))
    if bad:
        raise SystemExit(
            "a row was proved and later recorded unresolved, so 'prefer proved'\n"
            "and 'prefer latest' disagree. Decide by hand; do not let this\n"
            "script pick:\n  " + "\n  ".join(f"{s} {o}" for s, o in bad))


def main():
    covered = [b for b in BATCHES if complete(b)]
    skipped = [b for b in BATCHES if b not in covered]
    rows = draws(covered)
    by_row = {}
    for r in rows:
        by_row.setdefault(r["solution_id"], []).append(r)
    check(by_row)

    kept, dup_rows = [], 0
    for sid, rs in sorted(by_row.items()):
        # stable sort, so the last maximum is the latest campaign
        best = max(range(len(rs)), key=lambda i: (RANK.get(rs[i]["outcome"], 0), i))
        rec = dict(rs[best])
        rec["drawn_times"] = len(rs)
        rec["superseded"] = [
            {"campaign": o["campaign"], "outcome": o["outcome"],
             "attempts_used": o["attempts_used"], "seconds": o["seconds"]}
            for i, o in enumerate(rs) if i != best
        ]
        if len(rs) > 1:
            dup_rows += 1
        kept.append(rec)

    meta = {"campaigns": covered, "incomplete_and_excluded": skipped,
            "draw_records": len(rows), "distinct_rows": len(kept),
            "drawn_more_than_once": dup_rows,
            "proved": sum(1 for r in kept if r["outcome"] == "proved")}
    (HERE / "data" / "campaign_dedup.json").write_text(
        json.dumps(meta, indent=2) + "\n")

    out = HERE / "data" / "campaign_dedup.jsonl"
    with out.open("w") as fh:
        for r in kept:
            fh.write(json.dumps(r) + "\n")

    proved = sum(1 for r in kept if r["outcome"] == "proved")
    print(f"wrote {out.relative_to(HERE)}")
    print(f"  {len(rows)} draw records -> {len(kept)} distinct rows "
          f"({dup_rows} were drawn more than once)")
    print(f"  {proved}/{len(kept)} proved ({proved / len(kept):.0%}) over distinct rows")
    rescued = sum(1 for r in kept if r["outcome"] == "proved"
                  and any(s["outcome"] == "unresolved" for s in r["superseded"]))
    print(f"  {rescued} rows a later campaign closed after an earlier one missed them")
    per = Counter(r["campaign"] for r in kept)
    print("  kept records by campaign: "
          + "  ".join(f"{short(b)}={per.get(b, 0)}" for b in covered))
    if skipped:
        print("  excluded, not finished: " + " ".join(short(b) for b in skipped))


if __name__ == "__main__":
    main()
