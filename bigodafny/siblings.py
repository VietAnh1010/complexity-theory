"""Flag sibling rows whose Dafny converged despite different complexity labels.

The validator compares stdout. It cannot see that a translation reached the
right answer by the wrong algorithm. That defect is invisible to every gate in
this pipeline and it destroys the one thing the dataset claims: that each row
is a translation of *that* Python, carrying *that* Python's complexity label.

Two solutions of one problem exist precisely because their labels differ. If
their Dafny is near-identical, at least one is not a translation of its source.

Not every hit is a defect. Two Python solutions can implement the same algorithm
in different styles, and BigOBench's labels -- measured, not proven -- can
differ on identical algorithms through profiling noise. So this reports
candidates for review; it does not revert anything.
"""
from __future__ import annotations
import collections, difflib, json, re, sys
from pathlib import Path

from common import DATA, SOLUTIONS, log, read_jsonl, write_jsonl

THRESHOLD = 0.80


def _norm(text, is_dafny):
    if is_dafny and "method Solve(" in text:
        text = text.split("method Solve(", 1)[1]
    text = re.sub(r"//.*" if is_dafny else r"#.*", "", text)
    return re.sub(r"\s+", " ", text).strip()


def scan(threshold=THRESHOLD):
    ds = {r["solution_id"]: r for r in read_jsonl(DATA / "dataset.jsonl")}
    tasks = {t["solution_id"]: t for t in read_jsonl(DATA / "tasks.jsonl")}

    translated = collections.defaultdict(list)
    for sid, r in ds.items():
        p = SOLUTIONS / r["problem_id"] / f"{sid}.dfy"
        if p.exists() and "TODO: translate" not in p.read_text(encoding="utf-8"):
            translated[r["problem_id"]].append(sid)

    def dafny(sid):
        r = ds[sid]
        return _norm((SOLUTIONS / r["problem_id"] / f"{sid}.dfy")
                     .read_text(encoding="utf-8"), True)

    hits = []
    for pid, sids in translated.items():
        for i in range(len(sids)):
            for j in range(i + 1, len(sids)):
                a, b = sids[i], sids[j]
                if ds[a]["time_complexity_inferred"] == ds[b]["time_complexity_inferred"]:
                    continue
                d = difflib.SequenceMatcher(None, dafny(a), dafny(b)).ratio()
                if d <= threshold:
                    continue
                p = difflib.SequenceMatcher(
                    None, _norm(tasks[a]["solution_code"], False),
                    _norm(tasks[b]["solution_code"], False)).ratio()
                hits.append({"problem_id": pid, "a": a, "b": b,
                             "a_complexity": ds[a]["time_complexity_inferred"],
                             "b_complexity": ds[b]["time_complexity_inferred"],
                             "dafny_similarity": round(d, 3),
                             "python_similarity": round(p, 3)})
    hits.sort(key=lambda h: (h["python_similarity"], -h["dafny_similarity"]))
    write_jsonl(DATA / "sibling_review.jsonl", hits)
    log(f"sibling candidates: {len(hits)} pairs over "
        f"{len({h['problem_id'] for h in hits})} problems")
    log(f"  rows involved: {len({h['a'] for h in hits} | {h['b'] for h in hits})}")
    log("  lowest python similarity first -- review those first")
    for h in hits[:10]:
        log(f"    py={h['python_similarity']:.2f} dfy={h['dafny_similarity']:.2f}  "
            f"{h['a']} [{h['a_complexity']}] vs {h['b']} [{h['b_complexity']}]")
    return hits


if __name__ == "__main__":
    sys.exit(0 if scan() is not None else 1)
