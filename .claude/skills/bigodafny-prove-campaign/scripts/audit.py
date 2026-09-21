#!/usr/bin/env python3
"""Check a prove campaign's trajectories against the verifier, not the reports.

Run `python3 proofs.py` first -- it re-verifies every file in
`solutions-proved/` from scratch and writes `data/complexity_proofs.jsonl`.
This script joins that output to the campaign's manifest and trajectories and
reports every place they disagree.

    python3 audit.py --batch batches/prove-sample-2 --repo .

An agent's own report is not evidence. In the first campaign one agent's prose
said 9 proved where its trajectory said 10, and the files said 10.
"""

import argparse
import json
import os
import subprocess
import sys

RELATIONS = {"confirms", "looser-slack", "looser-structural", "contradicts", None}


def read_jsonl(path):
    if not os.path.exists(path):
        return []
    with open(path) as fh:
        return [json.loads(l) for l in fh if l.strip()]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--batch", required=True)
    ap.add_argument("--repo", default=".")
    args = ap.parse_args()

    manifest = {r["solution_id"]: r for r in read_jsonl(f"{args.batch}/manifest.jsonl")}
    traj = {}
    for name in sorted(os.listdir(args.batch)):
        if name.startswith("traj_") and name.endswith(".jsonl"):
            for row in read_jsonl(os.path.join(args.batch, name)):
                row["_slice"] = name[5:-6]
                traj[row["solution_id"]] = row

    proofs = {
        r["solution_id"]: r
        for r in read_jsonl(os.path.join(args.repo, "data/complexity_proofs.jsonl"))
    }

    rows, problems = [], []
    for sid, m in sorted(manifest.items()):
        t = traj.get(sid)
        p = proofs.get(sid)
        claimed = (t or {}).get("outcome")
        verified = bool(p and p.get("verified"))
        rec = {
            "solution_id": sid,
            "label": m["label"],
            "claimed": claimed or "not attempted",
            "verified": verified,
            "proved_bound": (p or {}).get("proved_bound"),
            "relation": (t or {}).get("relation"),
            "why_failed": (t or {}).get("why_failed"),
            "attempts_used": (t or {}).get("attempts_used"),
            "seconds": (t or {}).get("seconds"),
            "slice": (t or {}).get("_slice"),
        }
        rows.append(rec)
        if t is None:
            problems.append(f"{sid}: no trajectory entry")
        elif claimed == "proved" and not verified:
            problems.append(f"{sid}: claimed proved, verifier disagrees")
        elif claimed == "unresolved" and verified:
            problems.append(f"{sid}: claimed unresolved, but a verified proof exists")
        if t and t.get("relation") not in RELATIONS:
            problems.append(f"{sid}: relation {t.get('relation')!r} not in vocabulary")
        if t and t.get("relation") == "contradicts" and not t.get("relation_reason"):
            problems.append(f"{sid}: contradicts with no reason given")
        if p and p.get("assume_count"):
            problems.append(f"{sid}: proof carries {p['assume_count']} assume(s)")

    # The originals are the control. An agent that edited solutions/ to make a
    # proof close has proved nothing.
    dirty = subprocess.run(
        ["git", "status", "--porcelain", "--", "bigodafny/solutions"],
        cwd=os.path.join(args.repo, ".."),
        capture_output=True,
        text=True,
    ).stdout.strip()
    if dirty:
        problems.append("solutions/ is modified:\n" + dirty)

    proved = [r for r in rows if r["verified"]]
    summary = {
        "batch": args.batch,
        "drawn": len(manifest),
        "proved": len(proved),
        "unresolved": len(rows) - len(proved),
        "by_label": {},
        "by_relation": {},
        "obstacles": {},
        "problems": problems,
    }
    for r in rows:
        lab = summary["by_label"].setdefault(r["label"], {"drawn": 0, "proved": 0})
        lab["drawn"] += 1
        lab["proved"] += 1 if r["verified"] else 0
        if r["verified"]:
            key = r["relation"] or "unrecorded"
            summary["by_relation"][key] = summary["by_relation"].get(key, 0) + 1
        elif r["why_failed"]:
            summary["obstacles"][r["why_failed"]] = (
                summary["obstacles"].get(r["why_failed"], 0) + 1
            )

    with open(f"{args.batch}/audit.jsonl", "w") as fh:
        for r in rows:
            fh.write(json.dumps(r) + "\n")
    with open(f"{args.batch}/summary.json", "w") as fh:
        json.dump(summary, fh, indent=2, sort_keys=True)

    print(json.dumps({k: v for k, v in summary.items() if k != "problems"}, indent=2))
    if problems:
        print("\nPROBLEMS", file=sys.stderr)
        for p in problems:
            print("  " + p, file=sys.stderr)
        return 1
    print("\nno disagreement between trajectories and the verifier")
    return 0


if __name__ == "__main__":
    sys.exit(main())
