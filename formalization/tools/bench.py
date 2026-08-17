#!/usr/bin/env python3
"""Browse the BigO(Bench) test sets and scaffold a Rocq example file.

Stdlib only, no keys, matching the repo's sourcing rules. The test sets are
downloaded once into .cache/ (gitignored); nothing large is committed.

    python3 tools/bench.py fetch
    python3 tools/bench.py labels
    python3 tools/bench.py list --label 'O(n**2)' --max-chars 300
    python3 tools/bench.py show 5_100
    python3 tools/bench.py scaffold 5_100

Every field this script prints comes from the downloaded file. It never fills
a field from anywhere else; a missing key prints as MISSING.
"""

import argparse
import collections
import json
import os
import random
import re
import sys
import urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
CACHE = os.path.join(ROOT, ".cache")
EXAMPLES = os.path.join(ROOT, "theories", "Examples")
MANIFEST = os.path.join(ROOT, "samples", "manifest.jsonl")

BASE = "https://huggingface.co/datasets/facebook/BigOBench/resolve/main/data"
SETS = {
    "time": "time_complexity_test_set.jsonl",
    "space": "space_complexity_test_set.jsonl",
}


def cache_path(which):
    return os.path.join(CACHE, SETS[which])


def fetch(which):
    os.makedirs(CACHE, exist_ok=True)
    dest = cache_path(which)
    if os.path.exists(dest) and os.path.getsize(dest) > 0:
        print(f"cached: {dest} ({os.path.getsize(dest)} bytes)")
        return dest
    url = f"{BASE}/{SETS[which]}"
    print(f"fetching {url}")
    with urllib.request.urlopen(url, timeout=600) as r, open(dest, "wb") as f:
        while True:
            chunk = r.read(1 << 20)
            if not chunk:
                break
            f.write(chunk)
    print(f"wrote {dest} ({os.path.getsize(dest)} bytes)")
    return dest


def records(which):
    p = cache_path(which)
    if not os.path.exists(p):
        sys.exit(f"not downloaded: run `bench.py fetch --set {which}` first")
    with open(p) as f:
        for line in f:
            line = line.strip()
            if line:
                yield json.loads(line)


LABEL_KEY = {"time": "time_complexity_inferred",
             "space": "space_complexity_inferred"}


def get(rec, key):
    v = rec.get(key)
    return v if v is not None else "MISSING"


def cmd_labels(args):
    c = collections.Counter(get(r, LABEL_KEY[args.set]) for r in records(args.set))
    for label, n in c.most_common():
        print(f"{n:6d}  {label}")
    print(f"{sum(c.values()):6d}  TOTAL ({len(c)} classes)")


def cmd_list(args):
    rows = []
    for r in records(args.set):
        label = get(r, LABEL_KEY[args.set])
        if args.label and label != args.label:
            continue
        code = r.get("solution_code") or ""
        if args.max_chars and len(code) > args.max_chars:
            continue
        rows.append((len(code), get(r, "solution_id"), label,
                     get(r, "problem_name")))
    rows.sort()
    for size, sid, label, name in rows[: args.limit]:
        print(f"{size:6d}  {sid:14s} {label:18s} {name[:52]}")
    print(f"-- {len(rows)} match, showing {min(len(rows), args.limit)}")


def cmd_sample(args):
    """Draw a reproducible random sample.

    The five examples formalized first were each the SHORTEST solution in
    their label class, which skews hard toward one-liners. Any claim about how
    often the fitted labels are wrong needs a sample drawn like this one
    instead: seeded, uniform over the split, and fixed before anyone looks at
    the solutions.
    """
    rows = [(get(r, "solution_id"), get(r, LABEL_KEY[args.set]),
             len(r.get("solution_code") or ""), get(r, "problem_name"))
            for r in records(args.set)]
    rows.sort()  # deterministic order before seeding
    rng = random.Random(args.seed)
    picked = rng.sample(rows, min(args.n, len(rows)))
    print(f"# seed={args.seed} set={args.set} n={len(picked)} of {len(rows)}")
    for sid, label, size, name in picked:
        print(f"{sid:14s} {label:18s} {size:6d}  {name[:48]}")
    c = collections.Counter(label for _, label, _, _ in picked)
    print("# label mix: " + ", ".join(f"{k}={v}" for k, v in c.most_common()))


def find(which, solution_id):
    for r in records(which):
        if get(r, "solution_id") == solution_id:
            return r
    sys.exit(f"no solution_id {solution_id} in the {which} test set")


def cmd_show(args):
    r = find(args.set, args.solution_id)
    for k in ("solution_id", "problem_id", "problem_name",
              LABEL_KEY[args.set], "time_curve_coefficient"):
        if k in r:
            print(f"{k}: {get(r, k)}")
    print("\n--- solution_code ---")
    print(r.get("solution_code", "MISSING"))
    print("--- inputs_example ---")
    print(repr(r.get("inputs_example", "MISSING"))[:400])
    if args.description:
        print("--- description ---")
        print(r.get("description", "MISSING"))


# Rocq's lexer nests comments, so a Python "(*" (unpacking inside a call, as in
# `print(*B)`) opens a comment that never closes, and "*)" closes the doc
# comment early. Both appear in real Code Contests solutions. A space breaks
# the token without changing what a reader sees.
def sanitize(code):
    return code.replace("(*", "( *").replace("*)", "* )")


STUB = '''(** * S{ident} — verdict: TODO

    BigO(Bench) {which}_complexity_test_set
      solution_id   {sid}
      problem_name  {pname}
      fitted label  {label}

    Source solution{note}:

{code}

    COST MODEL. TODO — state where the ticks go and why. This is the only
    place unsoundness can enter; the monad guarantees the cost matches the
    code, not that the code matches Python.

    In particular decide, and write down:
      - what "n" is: a collection length, or the VALUE of an integer?
      - which Python primitives are not O(1) (str.count, slicing, "in" on a
        list, sorted, int arithmetic on bignums)
      - which are O(1) and must NOT be modelled as Rocq lists (list stores,
        dict get/put)
      - whether the worst case is attained on the size-indexed family below
*)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From BigOBench Require Import Cost Asymptotic.

(* TODO: model the algorithm in the cost monad. *)

(* TODO: the size-indexed cost, e.g.
Definition T (n : nat) : nat := cost (solve (List.seq 0 n)).
*)

(* TODO: the bound, and the verdict theorem — one of:
     Theta T (fun n => ...)                  (* Tight *)
     BigO2 (fun n _ => T n) (fun n m => ...) (* SoundLoose *)
     ~ BigO T (fun n => ...)                 (* UnsoundUnder *)
     ~ BigOmega T (fun n => ...)             (* UnsoundOver *)
*)
'''


def cmd_scaffold(args):
    r = find(args.set, args.solution_id)
    ident = args.solution_id
    if not re.fullmatch(r"[0-9]+_[0-9]+", ident):
        sys.exit(f"unexpected solution_id shape: {ident!r}")
    path = os.path.join(EXAMPLES, f"S{ident}.v")
    if os.path.exists(path) and not args.force:
        sys.exit(f"exists: {path} (use --force to overwrite)")

    raw = r.get("solution_code") or ""
    clean = sanitize(raw)
    note = ("" if clean == raw else
            ' (spaces inserted in "(*"/"*)" for Rocq\'s lexer)')
    body = "\n".join("      " + ln for ln in clean.splitlines())

    os.makedirs(EXAMPLES, exist_ok=True)
    with open(path, "w") as f:
        f.write(STUB.format(ident=ident, which=args.set, sid=ident,
                            pname=get(r, "problem_name"),
                            label=get(r, LABEL_KEY[args.set]),
                            note=note, code=body))
    print(f"wrote {path}")

    os.makedirs(os.path.dirname(MANIFEST), exist_ok=True)
    seen = set()
    if os.path.exists(MANIFEST):
        with open(MANIFEST) as f:
            seen = {json.loads(l)["solution_id"] for l in f if l.strip()}
    if ident not in seen:
        row = {"solution_id": ident,
               "problem_id": get(r, "problem_id"),
               "problem_name": get(r, "problem_name"),
               "test_set": args.set,
               "fitted_label": get(r, LABEL_KEY[args.set]),
               "solution_code": raw}
        with open(MANIFEST, "a") as f:
            f.write(json.dumps(row, sort_keys=True) + "\n")
        print(f"appended {ident} to {MANIFEST}")

    print("\nNext: add the file to _CoqProject and All.v, write the model, "
          "then add a Catalog.v row once a theorem backs it.")


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--set", choices=sorted(SETS), default="time")
    sub = ap.add_subparsers(dest="cmd", required=True)

    sub.add_parser("fetch").set_defaults(fn=lambda a: fetch(a.set))
    sub.add_parser("labels").set_defaults(fn=cmd_labels)

    p = sub.add_parser("list")
    p.add_argument("--label")
    p.add_argument("--max-chars", type=int, default=0)
    p.add_argument("--limit", type=int, default=30)
    p.set_defaults(fn=cmd_list)

    p = sub.add_parser("sample")
    p.add_argument("--n", type=int, default=30)
    p.add_argument("--seed", type=int, default=20260817)
    p.set_defaults(fn=cmd_sample)

    p = sub.add_parser("show")
    p.add_argument("solution_id")
    p.add_argument("--description", action="store_true")
    p.set_defaults(fn=cmd_show)

    p = sub.add_parser("scaffold")
    p.add_argument("solution_id")
    p.add_argument("--force", action="store_true")
    p.set_defaults(fn=cmd_scaffold)

    args = ap.parse_args()
    args.fn(args)


if __name__ == "__main__":
    main()
