"""Stage one batch for one arm (README.md § Run)."""
from __future__ import annotations
import argparse, json, re, subprocess, sys
from pathlib import Path

ARMS = Path(__file__).resolve().parent
sys.path.insert(0, str(ARMS.parent / "fuzz"))
import blind                                                         # noqa: E402  (puts bigodafny/ on sys.path)
from guard import CMD                                                # noqa: E402  fuzz/guard.py
from common import DATA, PRELUDE, ROOT as BIGODAFNY, read_jsonl      # noqa: E402
from hook import STAGE, FUZZ_TIME_LIMIT as TIME_LIMIT                 # noqa: E402
import stage                                                         # noqa: E402  (hook put its directory on sys.path)

ARM_NAMES = ("full", "nofuzz", "noguess", "base")


def write_prelude(root):
    lines = PRELUDE.read_text().splitlines(keepends=True)
    kept = [l for l in lines if not (stage.ROW_ID.search(l) and l.lstrip().startswith("//"))]
    if any(stage.ROW_ID.search(l) for l in kept):
        raise SystemExit("prelude still names a row outside a comment line")
    (root / "prelude.dfy").write_text("".join(kept))


def brief(arm, row, statement):
    return ((ARMS / arm / "PROMPT.md").read_text()
            .replace("{{DIR}}", str(row)).replace("{{PRELUDE}}", str(row.parent / "prelude.dfy"))
            .replace("{{FUZZ}}", CMD).replace("{{TIME_LIMIT}}", str(TIME_LIMIT))
            .replace("{{STATEMENT}}", statement))


def setup_row(arm, entry, task):
    row = STAGE / arm / entry["sid"]
    (row / "attempts").mkdir(parents=True)
    p = subprocess.run([str(blind.TOOL), "annotate", str(BIGODAFNY / entry["path"]), str(row / "row.dfy"),
                        "enable=functions,seq,arrays"], capture_output=True, text=True)
    if p.returncode:
        raise SystemExit(f"{entry['sid']}: annotate failed: {p.stderr.strip()}")
    text = re.sub(r'^include ".*prelude\.dfy"$', 'include "../prelude.dfy"', (row / "row.dfy").read_text(),
                  count=1, flags=re.M)
    files = {"row.dfy": text, "statement": task["description"]}
    blind.check_leaks(entry["sid"], task["time_complexity_inferred"], files)
    blind.check_leaks(entry["sid"], entry["truth"], files)
    (row / "row.dfy").write_text(text)
    (row / "proof.dfy").write_text(text)
    (row / "BRIEF.md").write_text(brief(arm, row, task["description"]))
    (row / "budget.json").write_text(json.dumps({"attempts": 0}))
    print(f"set up {row}")


def main():
    parser = argparse.ArgumentParser(prog="setup.py")
    parser.add_argument("--arm", required=True, choices=ARM_NAMES)
    parser.add_argument("--batch", required=True, help="a `batch` value in manifest.jsonl")
    args = parser.parse_args()
    if (STAGE / args.arm).exists():
        raise SystemExit(f"{STAGE / args.arm} exists: run collect.py first")
    entries = [e for e in read_jsonl(ARMS / "manifest.jsonl") if str(e["batch"]) == args.batch]
    if not entries:
        raise SystemExit(f"no rows in batch {args.batch}")
    tasks = {t["solution_id"]: t for t in read_jsonl(DATA / "tasks.jsonl")}
    (STAGE / args.arm).mkdir(parents=True)
    write_prelude(STAGE / args.arm)
    for entry in entries:
        setup_row(args.arm, entry, tasks[entry["sid"]])


if __name__ == "__main__":
    main()
