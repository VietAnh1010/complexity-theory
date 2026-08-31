"""Emit one .dfy stub per task, and the Python glue that drives it.

The stub is the authoring surface: a signature, the Python it must reproduce,
and a body that returns "". An unimplemented stub therefore compiles and fails
its tests, which is the behaviour we want -- "not translated yet" and "wrong"
are both test failures, never build failures.

Stubs are never overwritten. Once a .dfy has a real body, scaffolding again
leaves it alone.
"""
from __future__ import annotations
import sys
from pathlib import Path

from common import DATA, SOLUTIONS, event, log, read_jsonl

STUB_BODY = '  output := ""; // TODO: translate the Python above\n'


def comment_block(text, prefix="// "):
    return "".join(prefix + ln + "\n" for ln in text.rstrip("\n").split("\n"))


def stub_source(task, sig):
    head = (
        f"// {task['problem_name']}  (problem {task['problem_id']}, "
        f"solution {task['solution_id']})\n"
        f"// time complexity: {task['time_complexity_inferred']}\n"
        f"// python exact-diff baseline: {task.get('baseline', 'unmeasured')}\n"
        "//\n"
        "// Reproduce the Python program's entire stdout in `output`.\n"
        "//\n"
        "// --- Python ---------------------------------------------------------\n"
        f"{comment_block(task['solution_code'])}"
        "// --------------------------------------------------------------------\n"
        "\n"
        'include "../../prelude.dfy"\n'
        "import opened Prelude\n"
        "\n"
    )
    return head + sig["dafny"] + "\n{\n" + STUB_BODY + "}\n"


def scaffold(force=False):
    tasks = list(read_jsonl(DATA / "tasks.jsonl"))
    sigs = {s["problem_id"]: s for s in read_jsonl(DATA / "signatures.jsonl")}
    bpath = DATA / "baseline.jsonl"
    base = ({b["solution_id"]: b["python_status"] for b in read_jsonl(bpath)}
            if bpath.exists() else {})
    for t in tasks:
        t["baseline"] = base.get(t["solution_id"], "unmeasured")

    made = kept = skipped = 0
    for t in tasks:
        sig = sigs.get(t["problem_id"])
        if not sig or sig["status"] != "ok":
            skipped += 1
            continue
        path = SOLUTIONS / t["problem_id"] / f"{t['solution_id']}.dfy"
        if path.exists() and not force:
            kept += 1
            continue
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(stub_source(t, sig), encoding="utf-8")
        made += 1

    log(f"stubs: {made} written, {kept} left alone, {skipped} skipped "
        f"(no usable signature)")
    event("scaffold", written=made, kept=kept, skipped=skipped)
    return made


if __name__ == "__main__":
    scaffold(force="--force" in sys.argv)
