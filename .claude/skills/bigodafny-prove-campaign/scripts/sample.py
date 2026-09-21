#!/usr/bin/env python3
"""Draw a random sample of unproved `solutions/` rows and split it into slices.

Writes `manifest.jsonl` and `slice_<x>.jsonl` into the batch directory. Reads
only; it never touches `solutions/` or `solutions-proved/`.

    python3 sample.py --batch batches/prove-sample-2 --n 50 --seed 20260921 --slices 3

A row is eligible when all three hold:

  * its `.dfy` lives in `solutions/` (the clean partition),
  * `data/index.jsonl` gives it a time-complexity label,
  * it passes its own gate -- `validate.py` says `valid` for a strict row,
    `difftest.py` says `agrees` for a loose row,

and it has no proof overlay in `solutions-proved/`.

The eligible pool is sorted by solution id before sampling, so the seed alone
determines the draw.
"""

import argparse
import json
import os
import random
import string
import sys


def load_jsonl(path):
    out = {}
    if not os.path.exists(path):
        return out
    with open(path) as fh:
        for line in fh:
            line = line.strip()
            if line:
                row = json.loads(line)
                out[row["solution_id"]] = row
    return out


def dfy_files(root):
    """solution_id -> path, for every .dfy directly under a problem dir."""
    found = {}
    if not os.path.isdir(root):
        return found
    for pid in os.listdir(root):
        d = os.path.join(root, pid)
        if not os.path.isdir(d):
            continue
        for name in os.listdir(d):
            if name.endswith(".dfy"):
                found[name[:-4]] = os.path.join(root, pid, name)
    return found


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--batch", required=True, help="batch dir, created if absent")
    ap.add_argument("--n", type=int, default=50)
    ap.add_argument("--seed", type=int, required=True)
    ap.add_argument("--slices", type=int, default=3)
    ap.add_argument("--repo", default=".", help="bigodafny/ root")
    args = ap.parse_args()

    repo = args.repo
    labels = {
        sid: row.get("time_complexity_inferred")
        for sid, row in load_jsonl(os.path.join(repo, "data/index.jsonl")).items()
    }
    validation = load_jsonl(os.path.join(repo, "data/validation.jsonl"))
    difftest = load_jsonl(os.path.join(repo, "data/difftest.jsonl"))

    solutions = dfy_files(os.path.join(repo, "solutions"))
    # solutions-proved/ is an overlay over the partition, not a member of it.
    proved = set(dfy_files(os.path.join(repo, "solutions-proved")))
    proved |= set(dfy_files(os.path.join(repo, "solutions-proved/nlogn")))

    pool, excluded = [], []
    skipped = {"no-label": 0, "gate": 0, "proved": 0}
    for sid in sorted(solutions):
        if sid in proved:
            skipped["proved"] += 1
            continue
        label = labels.get(sid)
        if not label:
            skipped["no-label"] += 1
            excluded.append({"solution_id": sid, "why": "no-label"})
            continue
        if sid in difftest:
            split, gate = "loose", difftest[sid].get("status")
            ok = gate == "agrees"
        else:
            split, gate = "strict", validation.get(sid, {}).get("status")
            ok = gate == "valid"
        if not ok:
            # A row in solutions/ whose latest recorded gate result is negative
            # or missing. Not drawn, and not dropped silently either.
            skipped["gate"] += 1
            excluded.append(
                {"solution_id": sid, "why": "gate", "split": split, "gate": gate}
            )
            continue
        pool.append(
            {
                "solution_id": sid,
                "path": os.path.relpath(solutions[sid], repo),
                "label": label,
                "split": split,
                "gate": gate,
            }
        )

    if len(pool) < args.n:
        print(f"pool has {len(pool)} rows, asked for {args.n}", file=sys.stderr)
        return 1

    sample = random.Random(args.seed).sample(pool, args.n)
    sample.sort(key=lambda r: r["solution_id"])

    os.makedirs(args.batch, exist_ok=True)
    with open(os.path.join(args.batch, "manifest.jsonl"), "w") as fh:
        for row in sample:
            fh.write(json.dumps(row) + "\n")
    with open(os.path.join(args.batch, "excluded.jsonl"), "w") as fh:
        for row in excluded:
            fh.write(json.dumps(row) + "\n")

    names = string.ascii_lowercase[: args.slices]
    for i, name in enumerate(names):
        rows = sample[i :: args.slices]
        with open(os.path.join(args.batch, f"slice_{name}.jsonl"), "w") as fh:
            for row in rows:
                fh.write(json.dumps(row) + "\n")
        print(f"slice_{name}.jsonl  {len(rows)} rows")

    print(f"pool {len(pool)}  drawn {len(sample)}  seed {args.seed}")
    print("skipped: " + "  ".join(f"{k}={v}" for k, v in skipped.items()))
    return 0


if __name__ == "__main__":
    sys.exit(main())
