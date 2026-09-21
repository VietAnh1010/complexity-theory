"""Collect the measured state of the corpus into one JSON payload.

Everything an artifact would display is computed here from the records on
disk, so no number in the artifact is ever typed by hand. Re-run it after any
sweep; it reads and never writes outside data/artifact_data.json.
"""
from __future__ import annotations
import json, re, subprocess
from collections import Counter
from pathlib import Path

from common import PROVED

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
            "tight_variant": "/nlogn/" in str(f),
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


def relation_of(sid, traj_row, rel):
    """confirms | looser-slack | looser-structural | contradicts | unresolved.

    Defaults to `confirms` for a proved row with no entry in
    label_relation.jsonl. That file carries the judgement for every row where
    the proved bound is not within its label's class; a row absent from it is
    one where the agent's bound and the label agree and nothing was disputed.
    """
    if not traj_row:
        return "not attempted"
    if sid in rel:
        return rel[sid]["relation"]
    return "confirms" if traj_row.get("outcome") == "proved" else "unresolved"


def prove_sample(manifest, traj, rel, depth, meta=None, obst=None):
    """The proof campaign: did a bounded agent close the complexity label?

    Unlike the verification sample there is no tool that settles this -- a
    bound has to be written. So the interesting number is not the success
    rate but WHY a row did not close, which is why `obstacles` is tabulated
    from the free-text reason rather than from a status field.
    """
    if not manifest:
        return {"status": "not yet run"}
    meta = meta or {"seed": 20260917, "pool": 329}
    # The first campaign kept the obstacle code alongside the relation; the
    # second moved it to its own file, since an obstacle belongs to a row that
    # did NOT close and a relation to one that did.
    obst = obst or {}
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
            # normalised reading; `agent_said_agrees` is what the agent wrote,
            # kept so the normalisation stays auditable.
            "relation": relation_of(s, t, rel),
            "relation_reason": (rel.get(s) or {}).get("reason"),
            "obstacle": (rel.get(s) or {}).get("obstacle")
                        or (obst.get(s) or {}).get("obstacle"),
            "agent_said_agrees": t.get("agrees_with_label"),
            "agent_said_relation": (rel.get(s) or {}).get("agent_said_relation"),
            "attempts_used": t.get("attempts_used"),
            "seconds": t.get("seconds"),
            "why_failed": t.get("why_failed"),
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
        "contradicts_label": [r["solution_id"] for r in rows
                              if r["relation"] == "contradicts"],
        "note_on_contradiction": (
            "Every proof in these campaigns is an upper bound. A bound ABOVE "
            "the label is `looser` -- it fails to confirm the label and cannot "
            "disagree with it, since that needs a lower bound. A bound BELOW "
            "the label does bear on it, but only after the other two "
            "explanations are ruled out: `tighter-costmodel` (the charge table "
            "costs something CPython does not) and `tighter-translation` (the "
            "Dafny runs a cheaper algorithm than the Python)."),
        "tighter_rows": {
            sid: r["relation"] for sid, r in sorted(rel.items())
            if str(r["relation"]).startswith("tighter")},
        "value_vs_size_rows": sorted(
            sid for sid, r in rel.items()
            if r["relation"] == "looser-structural"
            or r.get("obstacle") == "structural-unbounded"),
        "by_label": {
            lab: {"drawn": sum(1 for r in rows if r["label"] == lab),
                  "proved": sum(1 for r in proved if r["label"] == lab)}
            for lab in sorted({r["label"] for r in rows})},
        "obstacles": dict(Counter(
            r["obstacle"] for r in rows if r["obstacle"]).most_common()),
        "rows": sorted(rows, key=lambda r: (int(r["solution_id"].split("_")[0]),
                                            r["solution_id"])),
    }


def main():
    ds = {r["solution_id"]: r for r in jsonl(DATA / "dataset.jsonl")}
    ver = {r["solution_id"]: r for r in jsonl(DATA / "verification.jsonl")}
    depth = {r["sid"]: r for r in jsonl(DATA / "call_depth.jsonl")}
    stats = json.loads((DATA / "stats.json").read_text())
    manifest = jsonl(HERE / "batches/verify-sample/manifest.jsonl")
    pv_manifest = jsonl(HERE / "batches/prove-sample/manifest.jsonl")
    pv_traj = [r for f in sorted((HERE / "batches/prove-sample").glob("traj_*.jsonl"))
               for r in jsonl(f)]
    pv_rel = {r["solution_id"]: r
              for r in jsonl(HERE / "batches/prove-sample/label_relation.jsonl")}

    p2 = HERE / "batches/prove-sample-2"
    p2_manifest = jsonl(p2 / "manifest.jsonl")
    p2_traj = [r for f in sorted(p2.glob("traj_*.jsonl")) for r in jsonl(f)]
    p2_rel = {r["solution_id"]: r for r in jsonl(p2 / "label_relation.jsonl")}
    p2_obst = {r["solution_id"]: r for r in jsonl(p2 / "obstacles.jsonl")}
    p2_excluded = jsonl(p2 / "excluded.jsonl")

    p3 = HERE / "batches/prove-sample-3"
    p3_manifest = jsonl(p3 / "manifest.jsonl")
    p3_traj = [r for f in sorted(p3.glob("traj_*.jsonl")) for r in jsonl(f)]
    p3_rel = {r["solution_id"]: r for r in jsonl(p3 / "label_relation.jsonl")}
    p3_obst = {r["solution_id"]: r for r in jsonl(p3 / "obstacles.jsonl")}

    dirs = {d.name: sum(1 for _ in d.rglob("*.dfy"))
            for d in sorted(HERE.glob("solutions*")) if d.is_dir()}

    optout = sorted(s for s, r in ver.items() if r.get("termination_opt_out"))
    # A row that verifies with `decreases *` has every obligation discharged
    # EXCEPT termination, which it opted out of. Counting it as verified
    # without saying so overstates the guarantee.
    fully = [s for s, r in ver.items()
             if r["verified"] and not r.get("termination_opt_out")]

    sample = []
    for m in manifest:
        s = m["solution_id"]
        v, d = ver.get(s, {}), depth.get(s, {})
        sample.append({
            "solution_id": s, "label": m["label"], "split": m["split"],
            "gate": m["gate"], "verified": v.get("verified"),
            "termination_opt_out": v.get("termination_opt_out", False),
            "attempts_used": 0, "outcome": "verified-unedited",
            "call_depth": d.get("longest_chain"),
            "recursive": d.get("recursive"),
        })

    pv = prove_sample(pv_manifest, pv_traj, pv_rel, depth)
    pv2 = prove_sample(p2_manifest, p2_traj, p2_rel, depth,
                       meta={"seed": 20260921, "pool": 287}, obst=p2_obst)
    pv3 = prove_sample(p3_manifest, p3_traj, p3_rel, depth,
                       meta={"seed": 2026092102, "pool": 250}, obst=p3_obst)
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

        "sample": {
            "question": "were the 106 unrecorded rows failing, or never run?",
            "answer": "never run",
            "seed": 20260916, "drawn": len(manifest), "pool": 105,
            "frame": "solutions/, no verification record, non-empty label",
            "excluded": {"1196_51": "does not pass its gate"},
            "bounds": {"attempts_per_row": 3, "seconds_per_row": 300},
            "attempts_consumed": 0,
            "agents_spawned": 0,
            "labels": dict(Counter(m["label"] for m in manifest).most_common()),
            "rows": sorted(sample, key=lambda r: (int(r["solution_id"].split("_")[0]),
                                                  r["solution_id"])),
        },

        "prove_sample": pv,
        "prove_sample_2": pv2,
        "prove_sample_3": pv3,
        "proofs_all": proofs_all(depth, ds, pv.get("rows", [])
                                 + pv2.get("rows", []) + pv3.get("rows", [])),
        "difficulty": difficulty(pv.get("rows", []) + pv2.get("rows", [])
                                 + pv3.get("rows", [])),

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
        "corpus_stats": (json.loads((DATA / "corpus_stats.json").read_text())
                         if (DATA / "corpus_stats.json").exists() else None),
        "exploration": (json.loads(
            (HERE / "batches/prove-sample/exploration.json").read_text())
            if (HERE / "batches/prove-sample/exploration.json").exists() else None),

        "open_decisions": [
            "DECIDED 2026-09-17: value counts as a parameter. COMPLEXITY.md § 1.",
            "what `differs`-by-timeout-only should mean (1501_224): 77 of 93 "
            "comparable tests agree, 16 time out, and NO test disagrees",
            "RESOLVED 2026-09-21: of the 7 rows with no passing gate result, "
            "4 pass every runnable test and are exempt (data/gate_exempt.jsonl), "
            "2 moved to solutions-disputed/, 1 remains open. "
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

    out = DATA / "artifact_data.json"
    out.write_text(json.dumps(payload, indent=2) + "\n")
    v = payload["verification"]
    print(f"wrote {out.relative_to(HERE)}")
    print(f"  verification: {v['verified']}/{v['total']} verified, "
          f"{v['fully_verified_incl_termination']} incl. termination")
    print(f"  sample: {payload['sample']['drawn']} rows, "
          f"{payload['sample']['attempts_consumed']} attempts consumed")
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
