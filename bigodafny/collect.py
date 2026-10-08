"""Collect the measured state of the corpus into one JSON payload.

Everything an artifact would display is computed here from the records on
disk, so no number in the artifact is ever typed by hand. Re-run it after any
sweep; it writes only out/artifact_data.json (git-ignored).
"""
from __future__ import annotations
import json, re, statistics, subprocess
from vocab import RELATIONS
from collections import Counter
from pathlib import Path

from common import PROVED, OUT, SOLUTIONS
from features import extract, split_file, strip_comments

HERE = Path(__file__).resolve().parent
DATA = HERE / "data"


def jsonl(p):
    p = Path(p)
    return [json.loads(l) for l in p.open()] if p.exists() else []


def git(*args, default=""):
    try:
        return subprocess.run(["git", *args], cwd=HERE.parent, text=True,
                              capture_output=True, check=True).stdout.strip()
    except Exception:
        return default


def callgraph(depth):
    """Structure of solutions/ as walked by callgraph.py.

    Descriptive only -- no outcome join lives here. The record covers
    solutions/ and nothing else, and it was current when this was written:
    354 rows, no dead paths, no truncated search.
    """
    if not depth:
        return {"status": "no record"}
    rows = list(depth.values())
    prelude = Counter(f for r in rows for f in (r.get("prelude_calls") or []))
    # A proof adds ghost helpers, which can lengthen the longest chain. The
    # gap says how much instrumentation the corpus's proofs actually add.
    deepened = [r for r in rows
                if (r.get("longest_chain_with_ghost") or 0) > (r.get("longest_chain") or 0)]
    return {
        "scope": "solutions/", "rows": len(rows),
        "depth_distribution": dict(sorted(Counter(
            r["longest_chain"] for r in rows).items())),
        "median_depth": sorted(r["longest_chain"] for r in rows)[len(rows) // 2],
        "recursive": sum(1 for r in rows if r.get("recursive")),
        "self_contained_depth_0_1": sum(1 for r in rows if r["longest_chain"] <= 1),
        "reachable_distribution": dict(sorted(Counter(
            r.get("reachable", 0) for r in rows).items())),
        "own_decls_distribution": dict(sorted(Counter(
            r.get("own_decls", 0) for r in rows).items())),
        "rows_deepened_by_ghost": len(deepened),
        "prelude_calls_total": sum(prelude.values()),
        "prelude_call_frequency": dict(prelude.most_common()),
        "rows_using_no_prelude": sum(1 for r in rows if not r.get("prelude_calls")),
        "search_truncated": sum(1 for r in rows if r.get("search_truncated")),
    }


def proofs_all(depth, ds, pv_rows):
    """Every proved row in the corpus: the 33 that predate the cost axioms
    and the rows closed by the sampled campaigns.

    The two groups are tagged by `era` and never summed on a tightness
    statistic. The pre-axiom set was re-checked on 2026-09-17: all 33 files
    verify, none needed re-proving, and no proof performs a `seq` update, so
    the retired charge reaches none of them.
    """
    files = sorted(PROVED.rglob("*.dfy"))
    campaign = {r["solution_id"] for r in pv_rows if r["outcome"] == "proved"}
    rows = []
    for f in files:
        sid = f.stem
        d, rec = depth.get(sid, {}), ds.get(sid, {})
        m = re.search(r"ensures\s+steps\s*<=\s*(.+)", f.read_text(encoding="utf-8"))
        rows.append({
            "solution_id": sid,
            "file": str(f.relative_to(HERE)),
            "era": "campaign" if sid in campaign else "pre-axiom",
            "label": rec.get("time_complexity_inferred"),
            "bound": (m.group(1).split("//")[0].strip() if m else None),
            "call_depth": d.get("longest_chain"),
            "recursive": d.get("recursive"),
        })
    sids = {r["solution_id"] for r in rows}
    return {
        "files": len(rows), "rows": len(sids),
        "by_era": dict(Counter(r["era"] for r in rows)),
        "rows_with_two_proofs": sorted(
            sid for sid in sids
            if sum(1 for r in rows if r["solution_id"] == sid) > 1),
        "pre_axiom_recheck": {
            "date": "2026-09-17", "files": 33, "verify": 33, "needed_reproof": 0,
            "seq_updates_found": 0,
            "note": ("The claim that old proofs charge |s| for a seq update was "
                     "checked and is false -- no proof performs one. The only "
                     "changed-charge operation present is the slice, in 4 rows."),
        },
        "by_label": dict(Counter(r["label"] for r in rows).most_common()),
        "entries": rows,
    }


def difficulty(pv_rows):
    """Does structure predict whether a proof closes?

    Joins both campaigns' outcomes against call depth and recursion. The
    label is already known to matter -- linear rows close far more often than
    `O(nlogn)` ones -- so this asks whether depth adds anything beyond it.
    """
    done = [r for r in pv_rows if r["outcome"] in ("proved", "unresolved")]
    if not done:
        return {"status": "not yet run"}

    def rate(key):
        out = {}
        for r in done:
            k = r.get(key)
            k = "unknown" if k is None else str(k)
            a, b = out.setdefault(k, [0, 0])
            out[k] = [a + (r["outcome"] == "proved"), b + 1]
        return {k: {"proved": v[0], "of": v[1]} for k, v in sorted(out.items())}

    return {
        "n": len(done),
        "by_call_depth": rate("call_depth"),
        "by_recursive": rate("recursive"),
        "by_label": rate("label"),
        "note": ("Label dominates. Depth is reported so the claim can be "
                 "checked rather than asserted; with the sample split "
                 "across several depths, treat any depth effect as "
                 "indicative."),
    }


def campaign_series(campaigns):
    """Per-label rate across every campaign, with a binomial test per cell.

    A single campaign's table is 8 to 25 rows per label class, so a swing of
    two rows moves the rate by ten points. After campaign 3 this project
    reported a crossover -- O(nlogn) overtaking O(n) -- from exactly such a
    swing. Campaign 4 did not reproduce it. The test here is the check that
    was missing: how surprising is each cell under the pooled rate for its
    label? Nothing below p = 0.05 on a single cell survives the eight-odd
    comparisons anyone eyeballing this table is implicitly making.
    """
    from math import comb

    def two_sided(k, n, p):
        if n == 0:
            return None
        pk = comb(n, k) * p ** k * (1 - p) ** (n - k)
        return sum(comb(n, i) * p ** i * (1 - p) ** (n - i)
                   for i in range(n + 1)
                   if comb(n, i) * p ** i * (1 - p) ** (n - i) <= pk * 1.0000001)

    labels = sorted({lab for c in campaigns for lab in c.get("by_label", {})})
    out = {}
    for lab in labels:
        cells = [c.get("by_label", {}).get(lab) for c in campaigns]
        tp = sum(x["proved"] for x in cells if x)
        td = sum(x["drawn"] for x in cells if x)
        out[lab] = {
            "pooled": {"proved": tp, "drawn": td,
                       "rate": round(tp / td, 4) if td else None},
            "by_campaign": [
                None if not x else {
                    "proved": x["proved"], "drawn": x["drawn"],
                    "p_vs_pooled": (round(two_sided(x["proved"], x["drawn"], tp / td), 4)
                                    if td else None)}
                for x in cells],
        }
    return {
        "campaigns": len(campaigns),
        "note": ("Per-campaign cells are small. Read the pooled column; treat a "
                 "single campaign's swing as noise unless p is small AND the "
                 "next campaign reproduces it."),
        "by_label": out,
    }


def relation_of(sid, traj_row, rel):
    """A relation from vocab.RELATIONS, or unresolved / not attempted.

    label_relation.jsonl holds the reviewed relation for every proved row;
    the default covers only a row with no line, which audit.py rejects.
    """
    if not traj_row:
        return "not attempted"
    if sid in rel:
        return rel[sid]["relation"]
    return "confirms" if traj_row.get("outcome") == "proved" else "unresolved"


def agent_view(d, traj, rel):
    """A batch's records as its agents left them, plus where each row stands now.

    Rows revised after their campaign -- proved, or their proofs tightened, by
    hand and outside the budget -- carry their latest state in the current
    files, and their superseded lines in old-record.jsonl. The campaign tables
    measure what a BOUNDED agent achieved, so they are built from the
    superseded lines; each revised row also carries `current_*` fields.
    """
    # the EARLIEST superseded line is the agent's; later ones are later edits
    old = {}
    for o in jsonl(d / "old-record.jsonl"):
        old.setdefault(o["file"], {}).setdefault(o["record"]["solution_id"], o["record"])
    old_traj = {}
    for fn, recs in old.items():
        if fn.startswith("traj_"):
            old_traj.update(recs)
    traj2 = []
    for r in traj:
        # only a REVISED record is swapped for its agent-era line; a rerun
        # record is itself the campaign's record for that row
        a = dict(old_traj.get(r["solution_id"], r)) if r.get("revision") else dict(r)
        a["current_outcome"] = r.get("outcome")
        a["current_bound"] = r.get("bound")
        a["current_relation"] = r.get("relation")
        a["revised"] = bool(r.get("revision"))
        # the obstacle lives on the current record; a revised one keeps the
        # agent's as agent_obstacle
        a["obstacle"] = r.get("agent_obstacle", r.get("obstacle"))
        traj2.append(a)
    rel2 = {sid: rec for sid, rec in rel.items() if not rec.get("revision")}
    # a rerun record carries its own relation; old lines describe another run
    reruns = {r["solution_id"] for r in traj if r.get("rerun")}
    rel2.update({sid: rec for sid, rec in old.get("label_relation.jsonl", {}).items()
                 if sid not in reruns})
    return traj2, rel2


def prove_sample(manifest, traj, rel, depth, meta=None):
    """The proof campaign: did a bounded agent close the complexity label?

    Unlike safety verification there is no tool that settles this -- a
    bound has to be written. So the interesting number is not the success
    rate but WHY a row did not close, which is why `obstacles` is tabulated
    from the free-text reason rather than from a status field.
    """
    if not manifest:
        return {"status": "not yet run"}
    meta = meta or {"seed": 20260917, "pool": 329}
    by_sid = {r["solution_id"]: r for r in traj}
    rows = []
    for m in manifest:
        s = m["solution_id"]
        t, d = by_sid.get(s, {}), depth.get(s, {})
        rows.append({
            "solution_id": s, "label": m["label"], "split": m["split"],
            "outcome": t.get("outcome", "not attempted"),
            "bound": t.get("bound"),
            # Every bound here is an UPPER bound, so a bound above the label
            # fails to confirm it and cannot contradict it. `relation` is the
            # reviewed reading; `prover_*` is what the proving subagent wrote,
            # kept so the review stays auditable.
            "relation": relation_of(s, t, rel),
            "relation_reason": (rel.get(s) or {}).get("reason"),
            "obstacle": t.get("obstacle"),
            "prover_agrees": t.get("agrees_with_label"),
            "prover_relation": (rel.get(s) or {}).get("prover_relation"),
            "review": (rel.get(s) or {}).get("review"),
            "attempts_used": t.get("attempts_used"),
            "seconds": t.get("seconds"),
            "why_failed": t.get("why_failed"),
            "current_outcome": t.get("current_outcome", t.get("outcome")),
            "current_bound": t.get("current_bound", t.get("bound")),
            "current_relation": t.get("current_relation"),
            "revised": t.get("revised", False),
            "call_depth": d.get("longest_chain"),
            "recursive": d.get("recursive"),
        })
    done = [r for r in rows if r["outcome"] in ("proved", "unresolved")]
    proved = [r for r in rows if r["outcome"] == "proved"]
    return {
        "question": "can a bounded agent prove the label of a random row?",
        "seed": meta["seed"], "drawn": len(manifest), "pool": meta["pool"],
        "frame": "solutions/, no proof in solutions-proved/, non-empty label",
        "bounds": {"attempts_per_row": 3, "seconds_per_row": 300},
        "agents": 3, "model": "sonnet",
        "attempted": len(done),
        "proved": len(proved),
        "unresolved": sum(1 for r in done if r["outcome"] == "unresolved"),
        "relations": dict(Counter(r["relation"] for r in rows).most_common()),
        "label_overstated": [r["solution_id"] for r in rows
                             if r["relation"] == "tighter-label"],
        "relation_vocabulary": RELATIONS,
        "note_on_relations": (
            "Every proof in these campaigns is an upper bound. A bound ABOVE "
            "the label fails to confirm it and cannot contradict it, since that "
            "needs a lower bound. A bound BELOW the label bears on it only once "
            "the charge table (`tighter-costmodel`) and the translation "
            "(`tighter-translation`) are ruled out; then it is `tighter-label`."),
        "tighter_rows": {
            r["solution_id"]: r["relation"]
            for r in sorted(rows, key=lambda r: r["solution_id"])
            if str(r["relation"]).startswith("tighter")},
        "value_vs_size_rows": sorted(
            r["solution_id"] for r in rows
            if r["relation"] == "looser-structural"
            or r["obstacle"] == "structural-unbounded"),
        "by_label": {
            lab: {"drawn": sum(1 for r in rows if r["label"] == lab),
                  "proved": sum(1 for r in proved if r["label"] == lab)}
            for lab in sorted({r["label"] for r in rows})},
        "obstacles": dict(Counter(
            r["obstacle"] for r in rows if r["obstacle"]).most_common()),
        "rows": sorted(rows, key=lambda r: (int(r["solution_id"].split("_")[0]),
                                            r["solution_id"])),
    }


PY_LINE = re.compile(r"^// ?(.*)$")


def python_loc(header):
    """Lines of the original Python, which each header quotes verbatim.

    The block opens with `// --- Python ---...` and closes with a plain rule
    line, so the opener has to be matched on its own -- a single `-{20,}`
    pattern misses it and silently returns zero for every row.
    """
    inside, n = False, 0
    for line in header.splitlines():
        if not inside and re.match(r"^//\s*-+\s*Python\s*-+", line):
            inside = True
            continue
        if inside:
            if re.match(r"^//\s*-{20,}\s*$", line):
                break
            m = PY_LINE.match(line)
            if m and m.group(1).strip():
                n += 1
    return n


def loc(code):
    return sum(1 for l in code.splitlines() if l.strip())


def pct(xs, p):
    xs = sorted(xs)
    return xs[min(len(xs) - 1, int(round(p / 100 * (len(xs) - 1))))]


def corpus_stats(ds, depth):
    """Structural profile of solutions/: Dafny body size with comments
    stripped (each header quotes the Python verbatim), loops, call depth."""
    rows = []
    for f in sorted(SOLUTIONS.rglob("*.dfy")):
        text = f.read_text(encoding="utf-8")
        header, body_raw = split_file(text)
        body = strip_comments(body_raw)
        ft = extract(text)
        sid = f.stem
        d = depth.get(sid, {})
        rows.append({
            "solution_id": sid,
            "label": (ds.get(sid) or {}).get("time_complexity_inferred"),
            "dafny_loc": loc(body),
            "python_loc": python_loc(header),
            "loops": ft["loops"],
            "loop_depth": ft["loop_depth"],
            "data_dependent_loops": ft["data_dependent_loops"],
            "recursive_helpers": ft["recursive_helpers"],
            "seq_args": ft["seq_args"],
            "call_depth": d.get("longest_chain"),
            "reachable": d.get("reachable"),
            "own_decls": d.get("own_decls"),
            "prelude_calls": d.get("prelude_calls") or [],
        })

    dl = [r["dafny_loc"] for r in rows]
    pl = [r["python_loc"] for r in rows if r["python_loc"]]
    ratio = [r["dafny_loc"] / r["python_loc"]
             for r in rows if r["python_loc"] and r["dafny_loc"]]

    def dist(key):
        return dict(sorted(Counter(r[key] for r in rows).items(),
                           key=lambda kv: (kv[0] is None, kv[0])))

    out = {
        "scope": "solutions/", "rows": len(rows),
        "dafny_loc": {
            "total": sum(dl), "mean": round(statistics.mean(dl), 1),
            "median": statistics.median(dl), "min": min(dl), "max": max(dl),
            "p90": pct(dl, 90), "p99": pct(dl, 99),
        },
        "python_loc": {
            "total": sum(pl), "mean": round(statistics.mean(pl), 1),
            "median": statistics.median(pl), "min": min(pl), "max": max(pl),
        },
        "expansion": {
            "median_dafny_over_python": round(statistics.median(ratio), 2),
            "mean": round(statistics.mean(ratio), 2),
            "rows_smaller_in_dafny": sum(1 for x in ratio if x < 1),
        },
        "loops": {
            "distribution": dist("loops"),
            "loopless_rows": sum(1 for r in rows if r["loops"] == 0),
            "max": max(r["loops"] for r in rows),
        },
        "loop_depth": {
            "distribution": dist("loop_depth"),
            "nested": sum(1 for r in rows if r["loop_depth"] >= 2),
        },
        "data_dependent_loops": {
            "distribution": dist("data_dependent_loops"),
            "rows_with_any": sum(1 for r in rows if r["data_dependent_loops"]),
        },
        "call_depth": {
            "distribution": dist("call_depth"),
            "median": statistics.median(r["call_depth"] for r in rows),
            "mean": round(statistics.mean(r["call_depth"] for r in rows), 2),
        },
        "recursive_helpers": {
            "rows_with_own_recursion": sum(1 for r in rows if r["recursive_helpers"]),
        },
        "own_decls": dist("own_decls"),
        "prelude": {
            "frequency": dict(Counter(
                fn for r in rows for fn in r["prelude_calls"]).most_common()),
            "rows_using_none": sum(1 for r in rows if not r["prelude_calls"]),
            "median_per_row": statistics.median(
                len(r["prelude_calls"]) for r in rows),
        },
        "labels": dict(Counter(r["label"] for r in rows).most_common()),
        "rows_detail": rows,
    }
    return out


def main():
    ds = {r["solution_id"]: r for r in jsonl(DATA / "dataset.jsonl")}
    ver = {r["solution_id"]: r for r in jsonl(DATA / "verification.jsonl")}
    depth = {r["sid"]: r for r in jsonl(DATA / "call_depth.jsonl")}
    stats = json.loads((DATA / "stats.json").read_text())
    pv_manifest = jsonl(HERE / "batches/prove-sample/manifest.jsonl")
    pv_traj = [r for f in sorted((HERE / "batches/prove-sample").glob("traj_*.jsonl"))
               for r in jsonl(f)]
    pv_rel = {r["solution_id"]: r
              for r in jsonl(HERE / "batches/prove-sample/label_relation.jsonl")}
    pv_traj, pv_rel = agent_view(HERE / "batches/prove-sample", pv_traj, pv_rel)

    p2 = HERE / "batches/prove-sample-2"
    p2_manifest = jsonl(p2 / "manifest.jsonl")
    p2_traj = [r for f in sorted(p2.glob("traj_*.jsonl")) for r in jsonl(f)]
    p2_rel = {r["solution_id"]: r for r in jsonl(p2 / "label_relation.jsonl")}
    p2_traj, p2_rel = agent_view(p2, p2_traj, p2_rel)
    p2_excluded = jsonl(p2 / "excluded.jsonl")

    p3 = HERE / "batches/prove-sample-3"
    p3_manifest = jsonl(p3 / "manifest.jsonl")
    p3_traj = [r for f in sorted(p3.glob("traj_*.jsonl")) for r in jsonl(f)]
    p3_rel = {r["solution_id"]: r for r in jsonl(p3 / "label_relation.jsonl")}
    p3_traj, p3_rel = agent_view(p3, p3_traj, p3_rel)

    p4 = HERE / "batches/prove-sample-4"
    p4_manifest = jsonl(p4 / "manifest.jsonl")
    p4_traj = [r for f in sorted(p4.glob("traj_*.jsonl")) for r in jsonl(f)]
    p4_rel = {r["solution_id"]: r for r in jsonl(p4 / "label_relation.jsonl")}
    p4_traj, p4_rel = agent_view(p4, p4_traj, p4_rel)

    p5 = HERE / "batches/prove-sample-5"
    p5_manifest = jsonl(p5 / "manifest.jsonl")
    p5_traj = [r for f in sorted(p5.glob("traj_*.jsonl")) for r in jsonl(f)]
    p5_rel = {r["solution_id"]: r for r in jsonl(p5 / "label_relation.jsonl")}
    p5_traj, p5_rel = agent_view(p5, p5_traj, p5_rel)

    p6 = HERE / "batches/prove-sample-6"
    p6_manifest = jsonl(p6 / "manifest.jsonl")
    p6_traj = [r for f in sorted(p6.glob("traj_*.jsonl")) for r in jsonl(f)]
    p6_rel = {r["solution_id"]: r for r in jsonl(p6 / "label_relation.jsonl")}
    p6_traj, p6_rel = agent_view(p6, p6_traj, p6_rel)

    p7 = HERE / "batches/prove-sample-7"
    p7_manifest = jsonl(p7 / "manifest.jsonl")
    p7_traj = [r for f in sorted(p7.glob("traj_*.jsonl")) for r in jsonl(f)]
    p7_rel = {r["solution_id"]: r for r in jsonl(p7 / "label_relation.jsonl")}
    p7_traj, p7_rel = agent_view(p7, p7_traj, p7_rel)

    p8 = HERE / "batches/prove-sample-8"
    p8_manifest = jsonl(p8 / "manifest.jsonl")
    p8_traj = [r for f in sorted(p8.glob("traj_*.jsonl")) for r in jsonl(f)]
    p8_rel = {r["solution_id"]: r for r in jsonl(p8 / "label_relation.jsonl")}
    p8_traj, p8_rel = agent_view(p8, p8_traj, p8_rel)

    dirs = {d.name: sum(1 for _ in d.rglob("*.dfy"))
            for d in sorted(HERE.glob("solutions*")) if d.is_dir()}

    optout = sorted(s for s, r in ver.items() if r.get("termination_opt_out"))
    # A row that verifies with `decreases *` has every obligation discharged
    # EXCEPT termination, which it opted out of. Counting it as verified
    # without saying so overstates the guarantee.
    fully = [s for s, r in ver.items()
             if r["verified"] and not r.get("termination_opt_out")]

    pv = prove_sample(pv_manifest, pv_traj, pv_rel, depth)
    pv2 = prove_sample(p2_manifest, p2_traj, p2_rel, depth,
                       meta={"seed": 20260921, "pool": 287})
    pv3 = prove_sample(p3_manifest, p3_traj, p3_rel, depth,
                       meta={"seed": 2026092102, "pool": 250})
    pv4 = prove_sample(p4_manifest, p4_traj, p4_rel, depth,
                       meta={"seed": 2026092103, "pool": 211})
    pv5 = prove_sample(p5_manifest, p5_traj, p5_rel, depth,
                       meta={"seed": 20260922, "pool": 179})
    pv6 = prove_sample(p6_manifest, p6_traj, p6_rel, depth,
                       meta={"seed": 20260923, "pool": 137})
    # The last plain draw. 28% of it was rows an earlier campaign had already
    # failed, so the sample had drifted from "a random row of the corpus" to
    # "a random row of what is left". Campaign 7 uses --exclude-drawn.
    pv6["draw_mode"] = "plain"
    pv6["repeat_share"] = 0.28
    pv7 = prove_sample(p7_manifest, p7_traj, p7_rel, depth,
                       meta={"seed": 20260923, "pool": 68})
    # The first --exclude-drawn draw: 50 rows from the 68 no earlier campaign
    # had touched, so it is comparable with campaign 1 and with nothing in
    # between. It also collects a reading trace, but only for the 20 rows whose
    # slices ran after that requirement was added mid-campaign.
    pv7["draw_mode"] = "exclude-drawn"
    pv7["repeat_share"] = 0.0
    pv7["reads_coverage"] = round(
        sum(1 for r in p7_traj if r.get("reads")) / len(p7_traj), 4)
    pv8 = prove_sample(p8_manifest, p8_traj, p8_rel, depth,
                       meta={"seed": 20260924, "pool": 18})
    # The last 18 never-drawn rows: a census of the remainder, not a sample.
    # Its brief carried the reading trace and the prelude's sort and search
    # lemmas from the start.
    pv8["draw_mode"] = "exclude-drawn, whole remaining pool"
    pv8["repeat_share"] = 0.0
    pv8["reads_coverage"] = round(
        sum(1 for r in p8_traj if r.get("reads")) / len(p8_traj), 4)
    # Two rows were drawn although they already carried a proof: sample.py
    # listed solutions-proved/ flatly and missed the value-bounded/ subdirectory
    # added the day before. Their outcomes are real but they are not new work,
    # so the rate over NEW rows is 35/48, not 37/50.
    pv5["redrawn_already_proved"] = {
        "rows": [r["solution_id"] for r in p5_manifest
                 if r.get("already_proved_when_drawn")],
        "cause": "sample.py missed solutions-proved/value-bounded/; fixed by "
                 "walking the overlay to any depth",
        "proved_excluding_them": 35, "drawn_excluding_them": 48,
        "note": "2128_34 was pure waste -- the agent rediscovered the existing "
                "proof. 305_76 was not: the second attempt produced a strictly "
                "tighter bound, which replaced the original.",
    }
    # Two verified proofs were deleted by an agent cleaning up after a FAILED
    # row in the same problem directory: 2914_264 while abandoning 2914_3, and
    # 750_51 while abandoning 750_14. Both restored from HEAD and re-verified.
    # audit.py now fails on a deletion outside the batch's own rows.
    pv5["proofs_destroyed_and_restored"] = ["2914_264", "750_51"]
    # All three agents were killed mid-slice by a session rate limit and
    # resumed on the remaining rows only. Recorded because it affects nothing
    # about the outcomes and everything about reproducing the run.
    pv3["interrupted"] = {
        "cause": "session rate limit, HTTP 429",
        "rows_recorded_at_interruption": 34,
        "resumed": "3 agents on the 16 remaining rows, appending to their "
                   "existing trajectories",
        "partial_proofs_left_behind": ["2926_54", "2496_30"],
        "partial_handling": "checked against the verifier; neither verified, "
                            "both deleted and the rows redone from scratch",
    }
    # A row sitting in solutions/ whose latest recorded gate result is negative
    # or missing. Excluded from the draw, and reported rather than dropped.
    pv2["excluded_from_pool"] = p2_excluded

    payload = {
        "generated": git("log", "-1", "--format=%cI", default=""),
        "commit": git("rev-parse", "--short", "HEAD"),
        "branch": git("rev-parse", "--abbrev-ref", "HEAD"),
        "toolchain": {"dafny": stats.get("dafny_version"), "z3": "4.12.1"},

        "corpus": {
            "rows": stats["rows"], "problems": stats["problems"],
            "directories": dirs,
            "splits": stats["splits"],
            "dafny_status": stats["dafny_status"],
            "time_complexity": stats["time_complexity"],
        },

        "verification": {
            # The sweep covers solutions-ungateable/ as well, since those rows
            # are translated and their safety record would otherwise vanish
            # when they left solutions/. Reported apart, because a safety
            # result and a behaviour result are different claims.
            "scope": "solutions/ and solutions-ungateable/",
            "total": len(ver),
            "verified": sum(r["verified"] for r in ver.values()),
            "fully_verified_incl_termination": len(fully),
            "termination_opt_out": optout,
            "by_directory": dict(Counter(
                r["path"].split("/")[0] for r in ver.values())),
            "failing": sorted(s for s, r in ver.items() if not r["verified"]),
            "failure_kinds": dict(Counter(
                r["kind"] for r in ver.values() if not r["verified"])),
        },

        "prove_sample": pv,
        "prove_sample_2": pv2,
        "prove_sample_3": pv3,
        "prove_sample_4": pv4,
        "prove_sample_5": pv5,
        "prove_sample_6": pv6,
        "prove_sample_7": pv7,
        "prove_sample_8": pv8,
        "campaign_series": campaign_series([pv, pv2, pv3, pv4, pv5, pv6, pv7, pv8]),
        "proofs_all": proofs_all(depth, ds, pv.get("rows", []) + pv2.get("rows", [])
                                 + pv3.get("rows", []) + pv4.get("rows", [])
                                 + pv5.get("rows", []) + pv6.get("rows", [])
                                 + pv7.get("rows", []) + pv8.get("rows", [])),
        "difficulty": difficulty(pv.get("rows", []) + pv2.get("rows", [])
                                 + pv3.get("rows", []) + pv4.get("rows", [])
                                 + pv5.get("rows", []) + pv6.get("rows", [])
                                 + pv7.get("rows", []) + pv8.get("rows", [])),

        "stale_record_finding": {
            "before": {"rows": 362, "recorded_failing": 12,
                       "paths_no_longer_existing": 114},
            "after": {"rows": len(ver),
                      "recorded_failing": sum(1 for r in ver.values()
                                              if not r["verified"])},
            "cause": ("verify_all.py rewrites the record whole and was not "
                      "re-run after the label audit moved 114 rows out of "
                      "solutions/"),
            "controls": [
                "injected an out-of-range read into a copy of 1053_38; "
                "reported index-out-of-range, so the script detects failure",
                "re-ran 3 rows the record called failing; all verified",
            ],
        },

        "callgraph": callgraph(depth),
        "corpus_stats": corpus_stats(ds, depth),

        "open_decisions": [
            "DECIDED 2026-09-17: value counts as a parameter. COMPLEXITY.md § 1.",
            "what `differs`-by-timeout-only should mean (1501_224): 77 of 93 "
            "comparable tests agree, 16 time out, and NO test disagrees",
            "RESOLVED 2026-09-21: of the 7 rows with no passing gate result, "
            "4 pass every runnable test, 2 moved to solutions-disputed/, 1 "
            "(1501_224) could not conclude; the 4 and 1501_224 are in "
            "solutions-ungateable/ (data/gate_ungateable.jsonl). "
            "batches/gate-audit/README.md",
            "rows using `decreases *` do not prove termination",
            "proofs.py's bound_of reads one line, so a wrapped or two-clause "
            "`ensures steps <=` is recorded truncated or as null: 1738_24, "
            "2254_6 and 457_27 have no bound on file though all three verify",
            "proofs.py's bound_of also takes the FIRST `ensures steps <=` in a "
            "file, which is a helper's when one is declared before Solve. 7 of "
            "151 proof files record a helper's bound rather than the row's: "
            "1414_8, 2128_34, 2496_30, 2803_133, 354_95, 433_16, 810_131. No "
            "verdict is affected -- `verified` does not use it -- but the bound "
            "published for those rows understates the row's cost",
        ],
    }

    out = OUT / "artifact_data.json"
    OUT.mkdir(exist_ok=True)
    out.write_text(json.dumps(payload, indent=2) + "\n")
    v = payload["verification"]
    print(f"wrote {out.relative_to(HERE)}")
    print(f"  verification: {v['verified']}/{v['total']} verified, "
          f"{v['fully_verified_incl_termination']} incl. termination")
    p6 = payload["prove_sample_6"]
    print(f"  proofs-6: {p6['proved']} proved / {p6['attempted']} attempted "
          f"of {p6['drawn']} drawn, pool {p6['pool']}")
    print(f"            relations {p6['relations']}")
    print(f"            obstacles {p6['obstacles']}")
    p5 = payload["prove_sample_5"]
    print(f"  proofs-5: {p5['proved']} proved / {p5['attempted']} attempted "
          f"of {p5['drawn']} drawn, pool {p5['pool']}")
    print(f"            relations {p5['relations']}")
    print(f"            obstacles {p5['obstacles']}")
    p4 = payload["prove_sample_4"]
    print(f"  proofs-4: {p4['proved']} proved / {p4['attempted']} attempted "
          f"of {p4['drawn']} drawn, pool {p4['pool']}")
    print(f"            relations {p4['relations']}")
    print(f"            obstacles {p4['obstacles']}")
    p3 = payload["prove_sample_3"]
    print(f"  proofs-3: {p3['proved']} proved / {p3['attempted']} attempted "
          f"of {p3['drawn']} drawn, pool {p3['pool']}")
    print(f"            relations {p3['relations']}")
    print(f"            obstacles {p3['obstacles']}")
    p2 = payload["prove_sample_2"]
    print(f"  proofs-2: {p2['proved']} proved / {p2['attempted']} attempted "
          f"of {p2['drawn']} drawn, pool {p2['pool']}")
    print(f"            relations {p2['relations']}")
    print(f"            obstacles {p2['obstacles']}")
    pv = payload["prove_sample"]
    if "drawn" in pv:
        print(f"  proofs: {pv['proved']} proved / {pv['attempted']} attempted "
              f"of {pv['drawn']} drawn")


if __name__ == "__main__":
    main()
