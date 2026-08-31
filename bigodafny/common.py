"""Paths, logging, JSONL IO. Shared by every bigodafny module."""
from __future__ import annotations
import json, os, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
CACHE = ROOT / ".cache"
DATA = ROOT / "data"
BUILD = ROOT / ".build"
SOLUTIONS = ROOT / "solutions"
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
