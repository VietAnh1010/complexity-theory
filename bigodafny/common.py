"""Paths, logging, JSONL IO. Shared by every bigodafny module."""
from __future__ import annotations
import json, os, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
CACHE = ROOT / ".cache"
DATA = ROOT / "data"
OUT = ROOT / "out"     # generated files nothing reads back; git-ignored
BUILD = ROOT / ".build"
# The seven status directories. Each row is in exactly one; each README says why.
SOLUTIONS = ROOT / "solutions"
UNSCREENED = ROOT / "solutions-unscreened"
UNVERIFIED = ROOT / "solutions-unverified"
UNTRANSLATED = ROOT / "solutions-untranslated"
DISPUTED = ROOT / "solutions-disputed"
UNGATEABLE = ROOT / "solutions-ungateable"
UNSURE = ROOT / "solutions-unsure"
# Not a status: copies of rows with a proved bound.
PROVED = ROOT / "solutions-proved"
PROVED_VALUE = PROVED / "value-bounded"

PRELUDE = ROOT / "prelude.dfy"
# One worker count for every gate, so a timeout means the same load in each.
WORKERS = 8

SOURCE_URL = ("https://huggingface.co/datasets/facebook/BigOBench/"
              "resolve/main/data/time_complexity_test_set.jsonl")
SOURCE_NAME = "time_complexity_test_set.jsonl"

DAFNY_VERSION = "4.11.0"


def z3_version():
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
    """Atomic, with sorted keys. With `key` (a field or tuple of fields), each line
    this write replaces or drops is first appended to old-record.jsonl beside it."""
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


# A test outside a limit quoted from the statement in data/constraints.jsonl is
# bogus; no gate counts it.
_SPEC, _FROM_STR = None, {}


def spec_tests(task, tiers):
    """(tier, test) pairs within the stated limits, and how many were skipped."""
    all_ = [(k, t) for k in tiers for t in task["tests"].get(k, [])]
    kept = [(k, t) for k, t in all_ if _in_spec(task, t["input"])]
    return kept, len(all_) - len(kept)


def _in_spec(task, test_input):
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
