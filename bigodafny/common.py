"""Paths, logging, JSONL IO. Shared by every bigodafny module."""
from __future__ import annotations
import json, os, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
CACHE = ROOT / ".cache"
DATA = ROOT / "data"
BUILD = ROOT / ".build"
SOLUTIONS = ROOT / "solutions"
# --- The status partition -------------------------------------------------
# These five are disjoint and cover all 640 dataset rows. A row is in exactly
# one of them, and which one says why it is not simply clean.
#
# Behaviourally valid, but the complexity label was never screened against the
# code: sibling-convergence candidates and set<T> users, quarantined before the
# label audit ran and not part of its 506 rows. Quarantined, not deleted.
# (was solutions-inexact/ -- "inexact" read as a claim about numbers.)
UNSCREENED = ROOT / "solutions-unscreened"
# Behaviourally valid, but `dafny verify` cannot discharge the obligations it
# raises with no user specification at all -- a seq index, a division, a
# decreases clause. Safe on the stored tests; unproven for every other input.
UNVERIFIED = ROOT / "solutions-unverified"
# Deliberately not translated. Each file states its blocker; there is no stub
# and no intent to fill one in. Kept so every dataset row has a file.
UNTRANSLATED = ROOT / "solutions-untranslated"
# Label audit queue. The audit screened this row and its stated complexity did
# not match what its Dafny costs; each file's header says which of the label or
# the translation looks wrong. Awaiting manual review, so the rows are NOT
# removed from the dataset -- every gate still runs on them and they still
# carry a label. (was solutions-tofix/ -- under the cost axioms most of these
# need no fix at all, so "tofix" overstated the verdict.)
DISPUTED = ROOT / "solutions-disputed"
# The gate cannot reach a verdict. Not "the translation failed" -- the stored
# test data fails first, so there is no evidence to be had: a test the
# problem's own Input.from_str rejects, or one where the row's own Python does
# not finish. Every gate still runs on these rows and they still carry a label;
# what is missing is the answer, not the row. See solutions-ungateable/README.md.
UNGATEABLE = ROOT / "solutions-ungateable"

# --- The proof overlay ----------------------------------------------------
# NOT part of the partition: an instrumented *copy* of a row that also lives in
# one of the five above. Complexity proved, not just tested: a ghost step
# counter with a proved bound. (was solutions-verified/, which collided with
# `dafny verify` -- that checks safety, this proves the label.)
PROVED = ROOT / "solutions-proved"
# Same rows, stronger proof: the true n log n via a recursion-tree argument.
# Nested inside the overlay rather than beside it, because it is a variant of a
# proof and not a status of its own. The simpler quadratic proof survives at
# solutions-proved/<pid>/<sid>.dfy alongside it.
PROVED_NLOGN = PROVED / "nlogn"

PRELUDE = ROOT / "prelude.dfy"

# The one upstream file this pipeline reads. Pinned by name, not by "latest".
SOURCE_URL = ("https://huggingface.co/datasets/facebook/BigOBench/"
              "resolve/main/data/time_complexity_test_set.jsonl")
SOURCE_NAME = "time_complexity_test_set.jsonl"

DAFNY_VERSION = "4.11.0"


def log(m):
    print(f"[{time.strftime('%H:%M:%S')}] {m}", file=sys.stderr, flush=True)


def event(kind, **f):
    DATA.mkdir(parents=True, exist_ok=True)
    rec = {"ts": time.strftime("%Y-%m-%dT%H:%M:%S"), "kind": kind, **f}
    with (DATA / "events.jsonl").open("a", encoding="utf-8") as fh:
        fh.write(json.dumps(rec, ensure_ascii=False) + "\n")


def read_jsonl(path):
    with Path(path).open(encoding="utf-8") as fh:
        for line in fh:
            if line.strip():
                yield json.loads(line)


def write_jsonl(path, rows):
    """Atomic, and with sorted keys so re-running is byte-identical."""
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    with tmp.open("w", encoding="utf-8") as fh:
        for r in rows:
            fh.write(json.dumps(r, ensure_ascii=False, sort_keys=True) + "\n")
    os.replace(tmp, path)
    return path


def write_json(path, obj):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(".tmp")
    tmp.write_text(json.dumps(obj, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
                   encoding="utf-8")
    os.replace(tmp, path)
    return path
