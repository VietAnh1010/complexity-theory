"""Assemble the evidence for a label audit, and act on the verdicts.

The question is whether a row's BigOBench complexity label describes what its
Dafny actually costs, under the measured cost model in `COMPLEXITY.md`.

Two stages, deliberately separated:

  `evidence`  deterministic. Extracts structural facts from each `.dfy` and
              pairs them with the label and the original Python. No model. Two
              runs produce byte-identical batches.
  `apply`     takes agent verdicts and moves mismatching rows to
              `solutions-disputed/`, one file per row, verdict recorded in the
              header so a human reviewer needs nothing else open.

A mismatch has two very different causes and the audit must say which, because
the repair differs:

  cause=label        the PYTHON is not the labelled class either. BigOBench's
                     label is wrong; the translation is faithful.
  cause=translation  the Python matches the label but the Dafny does not --
                     the classic case is `s := s[i := v]` in a loop, O(1) in
                     CPython and a full sequence copy in Dafny. Here the label
                     is right about the program it was measured on and the
                     TRANSLATION is the defect.

93 rows carry that seq-update pattern, so without the distinction the review
queue would be dominated by translation defects filed as label errors.
"""
from __future__ import annotations
import argparse, json, re, sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parent / "experiments"))
from common import DATA, ROOT, SOLUTIONS, log, read_jsonl, write_jsonl  # noqa: E402
from features import (class_risk, extract, split_file,                  # noqa: E402
                      strip_comments, accumulator_read_in_loop)

DISPUTED = ROOT / "solutions-disputed"
BATCHES = ROOT / "batches" / "labelaudit"

# Prelude functions whose cost is linear in their argument, not constant. An
# audit that treats these as O(1) will call a linear row constant.
LINEAR_PRELUDE = ["SumSeq", "MaxSeq", "MinSeq", "SumFrom", "MaxSeqFrom",
                  "MinSeqFrom", "ParseInt", "ParseInts", "ParseIntFrom",
                  "SplitWs", "SplitWsFrom", "Join", "JoinInts", "Repeat",
                  "ReplaceAll", "IntToString", "Gcd"]
SORTS = ["SortInts", "SortStrings", "Sort", "Merge"]


def facts(dfy_text):
    """Structural facts. Every one is checkable by eye against the file."""
    body = strip_comments(split_file(dfy_text)[1])
    f = extract(dfy_text)
    risk = class_risk(body)
    return {
        "loop_depth": f["loop_depth"],
        "loops": f["loops"],
        "data_dependent_loops": f["data_dependent_loops"],
        "decreases_star": "decreases *" in body,
        "seq_args": f["seq_args"],
        "body_lines": f["body_lines"],
        "recursive_helpers": f["recursive_helpers"],
        # cost-model tripwires, each measured in COMPLEXITY.md
        "seq_update_in_loop": risk["seq_update_in_loop"],
        "set_build_in_loop": risk["set_build_in_loop"],
        "seq_append_read_in_same_loop": accumulator_read_in_loop(body),
        "uses_map": bool(re.search(r"\bmap<", body)),
        "uses_set": bool(re.search(r"\bset<", body)),
        "uses_multiset": bool(re.search(r"\bmultiset\b", body)),
        "sorts": sorted({s for s in SORTS if re.search(rf"\b{s}\s*\(", body)}),
        "linear_prelude_calls": sorted(
            {s for s in LINEAR_PRELUDE if re.search(rf"\b{s}\s*\(", body)}),
    }


def evidence(limit=None, only=None, batch_size=20, prefix=None):
    # `--only` used to write batch_01.json like a full run does, which silently
    # overwrote the real batch 1 with whatever handful of rows was being
    # re-audited. A re-audit is a different thing from a batch and gets a
    # different name; the numbered batches are only ever written by a full run.
    if prefix is None:
        prefix = "batch" if not only else "reaudit"
    tasks = {t["solution_id"]: t for t in read_jsonl(DATA / "tasks.jsonl")}
    rows = []
    for p in sorted(SOLUTIONS.rglob("*.dfy"),
                    key=lambda q: (int(q.parent.name), q.stem)):
        sid = p.stem
        if only and sid not in only:
            continue
        t = tasks.get(sid)
        if t is None:
            continue
        text = p.read_text(encoding="utf-8")
        rows.append({
            "sid": sid,
            "problem_id": p.parent.name,
            "problem_name": t.get("problem_name"),
            "label": t["time_complexity_inferred"],
            "path": str(p.relative_to(ROOT)),
            "facts": facts(text),
            "dafny": text,
            "python": t.get("solution_code") or "",
            # A loop bounded by a value is only O(1) if the STATEMENT caps that
            # value. Without this an auditor falls back on contest convention,
            # which it flagged as a gap on 696_51, 681_105, 704_614 and 704_351.
            "description": (t.get("description") or "")[:4000],
        })
    if limit:
        rows = rows[:limit]

    BATCHES.mkdir(parents=True, exist_ok=True)
    batches = [rows[i:i + batch_size] for i in range(0, len(rows), batch_size)]
    for i, b in enumerate(batches, 1):
        (BATCHES / f"{prefix}_{i:02d}.json").write_text(
            json.dumps(b, indent=1), encoding="utf-8")
    log(f"evidence: {len(rows)} rows -> {len(batches)} batches in "
        f"{BATCHES.relative_to(ROOT)}")
    return batches


HEADER = """// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : {label}
//   audited class  : {true_class}
//   cause          : {cause}
//   confidence     : {confidence}
//   auditor        : {auditor}
//
//   {cause_gloss}
//
//   evidence:
{evidence}
//
//   how this label could be wrong, and what to check:
{what_to_look_for}
//
//   structural facts (deterministic, from labelaudit.py):
{facts}
// {rule}
"""

GLOSS = {
    "label": "The PYTHON is not the labelled class either. BigOBench's label "
             "looks wrong; the translation is faithful to it.",
    "translation": "The Python matches its label; the DAFNY does not. The "
                   "label is right about the program it was measured on and "
                   "the translation is the defect.",
    "harness": "Both artifacts are right. The Python pays to parse stdin and "
               "BigOBench profiled the whole script; the Dafny's Solve receives "
               "the inputs already parsed, so that cost is outside the measured "
               "method. Nothing to repair -- document it.",
    "both": "The Python does not match the label AND the translation diverges "
            "from the Python. Both need attention.",
    "unclear": "Which of the label or the translation is at fault was not "
               "determined by the audit.",
}


def _wrap(text, width=68, pre="//     "):
    out, cur = [], ""
    for w in str(text).split():
        if len(cur) + len(w) + 1 > width:
            out.append(pre + cur); cur = w
        else:
            cur = f"{cur} {w}".strip()
    if cur:
        out.append(pre + cur)
    return "\n".join(out) or (pre + "unavailable")


def apply(verdicts_path, dry_run=False):
    verdicts = [json.loads(l) for l in
                Path(verdicts_path).read_text(encoding="utf-8").splitlines()
                if l.strip()]
    tasks = {t["solution_id"]: t for t in read_jsonl(DATA / "tasks.jsonl")}
    moved, kept, missing = [], 0, []
    for v in verdicts:
        sid = v["sid"]
        t = tasks.get(sid)
        if t is None:
            missing.append(sid); continue
        src = SOLUTIONS / t["problem_id"] / f"{sid}.dfy"
        if not src.exists():
            missing.append(sid); continue
        if v.get("verdict") != "mismatch":
            kept += 1
            continue
        text = src.read_text(encoding="utf-8")
        head = HEADER.format(
            label=v.get("label") or t["time_complexity_inferred"],
            true_class=v.get("true_class") or "unstated",
            cause=v.get("cause") or "unclear",
            confidence=v.get("confidence") or "unstated",
            auditor=v.get("auditor") or "unstated",
            cause_gloss=_wrap(GLOSS.get(v.get("cause"), GLOSS["unclear"]),
                              pre="//   ").lstrip("/ "),
            evidence=_wrap(v.get("evidence")),
            what_to_look_for=_wrap(v.get("what_to_look_for")
                                   or "not recorded by this batch"),
            facts=_wrap(json.dumps(facts(text), sort_keys=True)),
            rule="-" * 68)
        dst = DISPUTED / t["problem_id"] / f"{sid}.dfy"
        if not dry_run:
            dst.parent.mkdir(parents=True, exist_ok=True)
            dst.write_text(head + "\n" + text, encoding="utf-8")
            src.unlink()
            try:
                src.parent.rmdir()          # only if now empty
            except OSError:
                pass
        moved.append({"sid": sid, "problem_id": t["problem_id"],
                      "label": t["time_complexity_inferred"],
                      "true_class": v.get("true_class"),
                      "cause": v.get("cause"), "confidence": v.get("confidence"),
                      "evidence": v.get("evidence")})
        log(f"  {sid:>10}  {t['time_complexity_inferred']:>14} -> "
            f"{v.get('true_class'):<14} cause={v.get('cause')}")
    if not dry_run:
        # MERGE, never overwrite. These files are the provenance of every move
        # ever made, and apply runs once per wave: a plain write silently
        # replaced round 1's 140 verdicts and 46 move records with round 2's,
        # which is a deletion of the audit trail rather than an update.
        # Keyed on solution_id so a re-audited row updates in place.
        def merge(path, new_rows, key="sid"):
            old = {r.get(key) or r.get("solution_id"): r
                   for r in read_jsonl(path)} if path.exists() else {}
            old.update({r.get(key) or r.get("solution_id"): r for r in new_rows})
            write_jsonl(path, list(old.values()))
            return len(old)
        n_v = merge(DATA / "label_audit.jsonl", verdicts)
        n_m = merge(DATA / "label_audit_moved.jsonl", moved)
        log(f"audit trail: {n_v} verdicts, {n_m} moves on record")
    log(f"apply: {len(moved)} moved to solutions-disputed/, {kept} kept"
        + (f", {len(missing)} not found: {missing}" if missing else "")
        + ("  [DRY RUN]" if dry_run else ""))
    return moved


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    e = sub.add_parser("evidence")
    e.add_argument("--limit", type=int)
    e.add_argument("--only", nargs="*")
    e.add_argument("--batch-size", type=int, default=20)
    e.add_argument("--prefix", help="output file stem; defaults to 'batch' for "
                                    "a full run and 'reaudit' with --only")
    a2 = sub.add_parser("apply")
    a2.add_argument("verdicts")
    a2.add_argument("--dry-run", action="store_true")
    a = ap.parse_args()
    if a.cmd == "evidence":
        evidence(a.limit, a.only, a.batch_size, a.prefix)
    else:
        apply(a.verdicts, a.dry_run)
