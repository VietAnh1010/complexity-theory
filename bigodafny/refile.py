"""Re-file audited rows after a change to the cost model.

Step 3 of `batches/cost-axioms/PLAN.md`. The charges became stipulated on
2026-09-16 (`COMPLEXITY.md` § 1), and a verdict is only as good as the model it
was written against: a row filed `translation` because a Dafny `seq` update
copies is no longer a defect, because the update is charged 1.

**This is not a re-audit.** Nothing here re-reads a row's Dafny to form a new
opinion. Each decision is derived from what the recorded verdict already says,
and the derivation is written down per row in
`batches/cost-axioms/refile_decisions.jsonl`, which is the input to this tool
and the audit trail for it. If you disagree with a move, argue with that file.

Three actions, and the second and third are why this is not a one-line filter:

  to_ok        every cost the verdict cited was a copying collection. The row
               leaves `solutions-disputed/` and its header block is stripped.
  reclassify   the copy charge dissolves but a different divergence survives,
               sometimes reversing direction. The row stays queued; its header
               is rewritten.
  to_mismatch  the row was filed `ok` only because the old charge reproduced
               the label by accident. It moves INTO the queue. The plan did not
               predict this direction; five rows take it.

Reversible: `--undo` is not offered, but every move is recorded in
`data/label_audit.jsonl` with a `refiled` block naming the prior verdict, so a
later session can reconstruct what changed and why.
"""
from __future__ import annotations
import argparse, json, re, sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from common import DATA, DISPUTED, ROOT, SOLUTIONS, log, read_jsonl, write_jsonl
import labelaudit                                              # noqa: E402

DECISIONS = ROOT / "batches" / "cost-axioms" / "refile_decisions.jsonl"
# `labelaudit.apply` closes its header with a rule of exactly 68 dashes.
RULE = re.compile(r"^// -{60,}\n", re.M)


def strip_header(text):
    """Drop the audit header block, returning the row as it was before `apply`.

    The header runs from the first line to the closing rule. Matching on the
    rule rather than counting lines survives a header whose evidence wrapped to
    a different number of lines, which is most of them.
    """
    if not text.startswith("// LABEL AUDIT"):
        return text, False
    m = RULE.search(text)
    if not m:
        return text, False
    rest = text[m.end():]
    return rest.lstrip("\n"), True


def header_for(v, tasks, body):
    t = tasks[v["sid"]]
    return labelaudit.HEADER.format(
        label=v.get("label") or t["time_complexity_inferred"],
        true_class=v.get("true_class") or "unstated",
        cause=v.get("cause") or "unclear",
        confidence=v.get("confidence") or "unstated",
        auditor=v.get("auditor") or "unstated",
        cause_gloss=labelaudit._wrap(
            labelaudit.GLOSS.get(v.get("cause"), labelaudit.GLOSS["unclear"]),
            pre="//   ").lstrip("/ "),
        evidence=labelaudit._wrap(v.get("evidence")),
        what_to_look_for=labelaudit._wrap(
            v.get("what_to_look_for") or "not recorded by this batch"),
        facts=labelaudit._wrap(json.dumps(labelaudit.facts(body), sort_keys=True)),
        rule="-" * 68)


def run(dry_run=False):
    decisions = read_jsonl(DECISIONS)
    tasks = {t["solution_id"]: t for t in read_jsonl(DATA / "tasks.jsonl")}
    audit = {r["sid"]: r for r in read_jsonl(DATA / "label_audit.jsonl")}
    moved = {r["sid"]: r for r in read_jsonl(DATA / "label_audit_moved.jsonl")}

    done, problems = [], []
    for d in decisions:
        sid, action = d["sid"], d["action"]
        t = tasks.get(sid)
        v = audit.get(sid)
        if t is None or v is None:
            problems.append(f"{sid}: no task or no verdict on record"); continue
        pid = t["problem_id"]
        src_disputed = DISPUTED / pid / f"{sid}.dfy"
        src_clean = SOLUTIONS / pid / f"{sid}.dfy"

        # Guard: the decision was written against a recorded verdict. If the
        # verdict moved since, the decision's premise is stale -- refuse rather
        # than apply it to something it was not reasoning about.
        #
        # Re-running this tool is the one exception, and it has to work: the
        # decision file is edited when a decision is found wrong, and the fix
        # has to reach rows already moved. A row whose `refiled` block names
        # this same action has had its files handled; only its record is
        # rewritten, from the corrected decision.
        was = d["was"]
        already = (v.get("refiled") or {}).get("action") == action
        if not already and (v["verdict"], v["cause"], v["true_class"]) != (
                was["verdict"], was["cause"], was["true_class"]):
            problems.append(
                f"{sid}: verdict on record is "
                f"{v['verdict']}/{v['cause']}/{v['true_class']}, decision "
                f"assumed {was['verdict']}/{was['cause']}/{was['true_class']}")
            continue

        now = d["now"]
        new_v = dict(v)
        new_v.update({k: val for k, val in now.items()})
        new_v["refiled"] = {"on": "2026-09-16", "action": action,
                            "was": was, "reason": d["reason"],
                            "model": "cost-axioms (COMPLEXITY.md section 1)"}

        if action == "to_ok":
            if already and src_clean.exists() and not src_disputed.exists():
                pass                      # files already moved on an earlier run
            elif not src_disputed.exists():
                problems.append(f"{sid}: not in solutions-disputed/"); continue
            else:
                body, had = strip_header(src_disputed.read_text(encoding="utf-8"))
                if not had:
                    problems.append(f"{sid}: no audit header to strip"); continue
                if not dry_run:
                    src_clean.parent.mkdir(parents=True, exist_ok=True)
                    src_clean.write_text(body, encoding="utf-8")
                    src_disputed.unlink()
                    try:
                        src_disputed.parent.rmdir()
                    except OSError:
                        pass
            moved.pop(sid, None)

        elif action == "to_mismatch":
            if not src_clean.exists() and not (already and src_disputed.exists()):
                problems.append(f"{sid}: not in solutions/"); continue
            body = src_clean.read_text(encoding="utf-8") if src_clean.exists() else None
            if body is not None and body.startswith("// LABEL AUDIT"):
                problems.append(f"{sid}: already carries a header"); continue
            if body is not None and not dry_run:
                src_disputed.parent.mkdir(parents=True, exist_ok=True)
                src_disputed.write_text(
                    header_for(new_v, tasks, body) + "\n" + body, encoding="utf-8")
                src_clean.unlink()
                try:
                    src_clean.parent.rmdir()
                except OSError:
                    pass
            moved[sid] = {"sid": sid, "problem_id": pid,
                          "label": t["time_complexity_inferred"],
                          "true_class": new_v["true_class"],
                          "cause": new_v["cause"],
                          "confidence": new_v["confidence"],
                          "evidence": new_v["evidence"]}

        elif action == "reclassify":
            if not src_disputed.exists():
                problems.append(f"{sid}: not in solutions-disputed/"); continue
            body, had = strip_header(src_disputed.read_text(encoding="utf-8"))
            if not had:
                problems.append(f"{sid}: no audit header to rewrite"); continue
            if not dry_run:
                src_disputed.write_text(
                    header_for(new_v, tasks, body) + "\n" + body, encoding="utf-8")
            moved[sid] = {**moved.get(sid, {"sid": sid, "problem_id": pid,
                                            "label": t["time_complexity_inferred"],
                                            "evidence": new_v["evidence"]}),
                          "true_class": new_v["true_class"],
                          "cause": new_v["cause"],
                          "confidence": new_v["confidence"]}
        else:
            problems.append(f"{sid}: unknown action {action!r}"); continue

        audit[sid] = new_v
        done.append((action, sid, was["true_class"], new_v["true_class"]))
        log(f"  {action:<12} {sid:>10}  {was['verdict']}/{was['cause'] or '-'}"
            f" -> {new_v['verdict']}/{new_v['cause'] or '-'}"
            f"  class {was['true_class']} -> {new_v['true_class']}")

    if not dry_run:
        write_jsonl(DATA / "label_audit.jsonl", list(audit.values()))
        write_jsonl(DATA / "label_audit_moved.jsonl", list(moved.values()))

    from collections import Counter
    log(f"refile: {len(done)} applied {dict(Counter(a for a, *_ in done))}"
        + ("  [DRY RUN]" if dry_run else ""))
    log(f"  solutions-disputed/ now holds {len(moved)} rows")
    if problems:
        log(f"  {len(problems)} NOT applied:")
        for p in problems:
            log(f"    {p}")
    return done, problems


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args()
    _, probs = run(dry_run=a.dry_run)
    sys.exit(1 if probs else 0)
