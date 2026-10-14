"""Paths, logging, JSONL IO. Shared by every bigodafny module."""
from __future__ import annotations
import json, os, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
CACHE = ROOT / ".cache"
DATA = ROOT / "data"
OUT = ROOT / "out"     # generated snapshots nothing reads back; git-ignored
BUILD = ROOT / ".build"
SOLUTIONS = ROOT / "solutions"
# --- The status partition -------------------------------------------------
# These seven are disjoint and cover all 640 dataset rows. A row is in exactly
# one of them, and which one says why it is not simply clean.
#
# Behaviourally valid, but the complexity label was never screened against the
# code: sibling-convergence candidates and set<T> users, quarantined before the
# label audit ran and not part of its 506 rows. Quarantined, not deleted.
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
# carry a label.
DISPUTED = ROOT / "solutions-disputed"
# The gate cannot reach a verdict. Not "the translation failed" -- the stored
# test data fails first, so there is no evidence to be had: a test the
# problem's own Input.from_str rejects, or one where the row's own Python does
# not finish. Every gate still runs on these rows and they still carry a label;
# what is missing is the answer, not the row. See solutions-ungateable/README.md.
UNGATEABLE = ROOT / "solutions-ungateable"
# The label audit could not decide (verdict `unsure`). Valid and verified like
# solutions/, but the label is neither confirmed nor disputed; a reviewer
# moves each row to solutions/ or solutions-disputed/. See its README.md.
UNSURE = ROOT / "solutions-unsure"

# --- The proof overlay ----------------------------------------------------
# NOT part of the partition: an instrumented *copy* of a row that also lives in
# one of the seven above. Complexity proved, not just tested: a ghost step
# counter with a proved bound. `dafny verify` checks safety; this proves the label.
PROVED = ROOT / "solutions-proved"
# Rows whose proved bound depends on the MAGNITUDE of an input, not only on how
# many inputs there are. Queued for review: BigOBench fitted its labels by
# profiling, which treats a capped value as constant, and COMPLEXITY.md
# section 1 decides the opposite, so the two disagree here by construction.
# A subdirectory of the overlay, not a status of its own -- the row still
# lives wherever the partition puts it.
PROVED_VALUE = PROVED / "value-bounded"

PRELUDE = ROOT / "prelude.dfy"
# Parallel jobs for every gate that checks rows independently. One number, so a
# timeout seen under one gate is not an artifact of a different load in another.
WORKERS = 8

# The one upstream file this pipeline reads. Pinned by name, not by "latest".
SOURCE_URL = ("https://huggingface.co/datasets/facebook/BigOBench/"
              "resolve/main/data/time_complexity_test_set.jsonl")
SOURCE_NAME = "time_complexity_test_set.jsonl"

DAFNY_VERSION = "4.11.0"


def z3_version():
    """The Z3 that `dafny` will find on PATH, as `z3 --version` reports it."""
    import subprocess
    try:
        out = subprocess.run(["z3", "--version"], capture_output=True, text=True).stdout
    except FileNotFoundError:
        return None
    parts = out.split()
    return parts[2] if len(parts) > 2 else out.strip() or None


def log(m):
    print(f"[{time.strftime('%H:%M:%S')}] {m}", file=sys.stderr, flush=True)


def read_jsonl(path):
    with Path(path).open(encoding="utf-8") as fh:
        for line in fh:
            if line.strip():
                yield json.loads(line)


def write_jsonl(path, rows, key=None, why=None):
    """Atomic, and with sorted keys so re-running is byte-identical.

    With `key` (a field, or a tuple of fields, naming a line), every line this
    write replaces or drops is appended to old-record.jsonl beside the file
    first. Records are history; a rewrite must never be the only copy."""
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    if key and path.exists():
        k = (lambda r: tuple(r.get(f) for f in key)) if isinstance(key, tuple) \
            else (lambda r: r.get(key))
        new = {k(r): r for r in rows}
        with (path.parent / "old-record.jsonl").open("a", encoding="utf-8") as fh:
            for r in read_jsonl(path):
                if new.get(k(r)) != r:
                    fh.write(json.dumps({
                        "file": path.name,
                        "superseded_on": time.strftime("%Y-%m-%d"),
                        "why": why or f"rewritten by {Path(sys.argv[0]).name}",
                        "record": r}, ensure_ascii=False) + "\n")
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


# --- Tests outside the problem's stated limits ------------------------------
# BigOBench ships tests that break the limits their own problem statement sets
# (1501: `1 <= k <= 10000`, tests up to 10**12). The code was written for the
# stated limits, so such a test is bogus and no gate counts it. Only a limit
# quoted from the statement in data/constraints.jsonl excludes a test; with no
# entry, every test counts. Callers record how many they skipped.
_SPEC, _FROM_STR = None, {}


def in_spec(task, test_input):
    global _SPEC
    if _SPEC is None:
        p = DATA / "constraints.jsonl"
        _SPEC = ({r["problem_id"]: r["check"] for r in read_jsonl(p)}
                 if p.exists() else {})
    pid = task["problem_id"]
    if pid not in _SPEC:
        return True
    if pid not in _FROM_STR:
        ns = {}
        exec(compile(task["dataclass_code"], "<dc>", "exec"), ns)  # needs numpy
        _FROM_STR[pid] = ns["Input"].from_str
    try:
        i = _FROM_STR[pid](test_input)
    except Exception:
        return True     # unparseable is the gates' own business, not a limit
    if eval(_SPEC[pid], {}, {"i": i}):
        return True
    # The public tests are the statement's own examples.
    if any(t["input"] == test_input for t in task["tests"].get("public_tests", [])):
        raise SystemExit(f"constraints.jsonl: problem {pid}'s check rejects "
                         "a statement example; the check is wrong")
    return False
