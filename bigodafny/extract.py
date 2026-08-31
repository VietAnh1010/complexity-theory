"""Download time_complexity_test_set.jsonl and project it into tasks.jsonl.

One task per (problem_id, solution_id). No model, no network beyond the one
file, and re-running must produce a byte-identical tasks.jsonl.
"""
from __future__ import annotations
import re, subprocess, sys
from collections import Counter

from common import (CACHE, DATA, SOURCE_NAME, SOURCE_URL, event, log,
                    read_jsonl, write_jsonl)

# Descriptions that permit more than one correct output. Byte-diff validation
# rejects correct translations of these, so they are split out rather than
# scored. This is a lexical heuristic: it has both false positives (the phrase
# appears while the output is in fact unique) and false negatives (the problem
# admits several answers without saying so). Do not treat the split as sound.
NONDET = re.compile(
    r"if there are (several|multiple|many)"
    r"|print any|output any|any of them|any one of|any such"
    r"|in any order"
    r"|if there are.*answers",
    re.I,
)

KEEP = ("problem_id", "solution_id", "problem_name", "description",
        "solution_code", "dataclass_code", "inputs_example",
        "time_complexity_inferred", "time_curve_coefficient", "tests")


def fetch(force=False):
    """Cache the upstream file. 82 MB; skipped when already present."""
    CACHE.mkdir(parents=True, exist_ok=True)
    dest = CACHE / SOURCE_NAME
    if dest.exists() and not force:
        log(f"cached {dest} ({dest.stat().st_size} bytes)")
        return dest
    log(f"downloading {SOURCE_URL}")
    subprocess.run(["curl", "-sS", "-L", "--fail", SOURCE_URL, "-o", str(dest)],
                   check=True)
    event("fetch", path=str(dest), bytes=dest.stat().st_size)
    log(f"fetched {dest.stat().st_size} bytes")
    return dest


def extract():
    src = fetch()
    rows = list(read_jsonl(src))
    log(f"read {len(rows)} source rows")

    tasks = []
    for r in rows:
        missing = [k for k in KEEP if k not in r]
        if missing:
            event("row_missing_fields", solution_id=r.get("solution_id"),
                  missing=missing)
            continue
        t = {k: r[k] for k in KEEP}
        # Verified upstream over all 640 rows; assert rather than recompute, so
        # a change in the source surfaces as a failure instead of silent drift.
        assert t["solution_id"].split("_")[0] == t["problem_id"], t["solution_id"]
        assert t["inputs_example"] == t["tests"]["public_tests"][0]["input"]
        # Only a hint. The split itself is assigned in dataset.py from the
        # measured Python baseline -- as a predictor of "the stored output is
        # not the only accepted answer" this regex scores precision 0.38,
        # recall 0.45, which is not good enough to gate a dataset on.
        t["nondet_hint"] = bool(NONDET.search(t["description"]))
        t["n_tests"] = {k: len(v) for k, v in t["tests"].items()}
        tasks.append(t)

    tasks.sort(key=lambda t: (int(t["problem_id"]), t["solution_id"]))
    out = write_jsonl(DATA / "tasks.jsonl", tasks)

    # tasks.jsonl is ~79 MB, almost all of it stored test I/O, and it is
    # regenerable byte-for-byte from the cached download. It stays out of git;
    # this index is the committed manifest of what the pool contains.
    write_jsonl(DATA / "index.jsonl", [
        {k: t[k] for k in ("problem_id", "solution_id", "problem_name",
                           "time_complexity_inferred", "time_curve_coefficient",
                           "n_tests", "nondet_hint")}
        for t in tasks])

    probs = {t["problem_id"] for t in tasks}
    hinted = sum(t["nondet_hint"] for t in tasks)
    event("extract", rows=len(tasks), problems=len(probs), nondet_hint=hinted)
    log(f"wrote {out}: {len(tasks)} rows over {len(probs)} problems")
    log(f"  nondet_hint set on {hinted} rows (a hint, not the split)")
    return tasks


if __name__ == "__main__":
    sys.exit(0 if extract() else 1)
