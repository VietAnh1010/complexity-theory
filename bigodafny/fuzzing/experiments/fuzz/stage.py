"""Stage rows for blind agents: one directory per row, outside the repository.

    python3 experiments/fuzz/stage.py ROOT SID [SID ...]

ROOT/<sid>/ gets `annotate`'s output as `row.dfy` (Python header, no label),
a copy of the prelude, the problem statement, `BRIEF.md` filled in, and two
wrappers, `fuzz` and `trace`, that call this repository's tools so the agent
never names a path in it. Then every staged file is scanned for the row's
label and for label-audit text; a hit aborts the staging.

Run the agents as the `blind-fuzz` agent type; its hook (`guard.py`)
confines them to the root that `out/fuzz-confined` names:

    echo ROOT > ../out/fuzz-confined
"""
from __future__ import annotations
import re, shutil, stat, subprocess, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
FUZZING = HERE.parents[1]
sys.path.insert(0, str(FUZZING.parent))
from common import DATA, PRELUDE, read_jsonl                          # noqa: E402

TOOL = FUZZING / "DafnySteps" / "bin" / "Release" / "net10.0" / "DafnySteps"
PY = FUZZING.parent / ".venv" / "bin" / "python3"
LEAKS = re.compile(r"time complexity|time_complexity|label|audit|BigOBench", re.I)

FUZZ = """#!/usr/bin/env bash
# ./fuzz FILE.dfy gen.py [--per N] [--timeout S]: run gen.py's inputs on FILE.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
exec {py} {run} {sid} --dfy "$here/$1" --gen "$here/$2" --out "$here/run-$(basename "$1" .dfy)" "${{@:3}}"
"""
TRACE = """#!/usr/bin/env bash
# ./trace FILE.dfy INPUT.txt LINE,LINE: run one input; log steps at those lines.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
log="$here/events-$(basename "$1" .dfy)-$(basename "$2" .txt).tsv"
cd {fuzzing}
exec {py} steptrace.py {sid} --dfy "$here/$1" --input "$here/$2" --trace "$3" --log "$log"
"""


def find_row(sid):
    pid = sid.split("_")[0]
    for d in sorted(FUZZING.parent.glob("solutions*")):
        if d.name != "solutions-proved" and (d / pid / f"{sid}.dfy").exists():
            return d / pid / f"{sid}.dfy"
    raise SystemExit(f"{sid}: no row")


def stage(root, sid, task):
    d = root / sid
    d.mkdir(parents=True, exist_ok=False)
    p = subprocess.run([str(TOOL), "annotate", str(find_row(sid)), str(d / "row.dfy"),
                        "enable=functions,seq,arrays"], capture_output=True, text=True)
    if p.returncode:
        raise SystemExit(f"{sid}: annotate failed: {p.stderr.strip()}")
    row = (d / "row.dfy").read_text()
    row = re.sub(r'^include ".*prelude\.dfy"$', 'include "prelude.dfy"', row, count=1, flags=re.M)
    (d / "row.dfy").write_text(row)
    shutil.copy(PRELUDE, d / "prelude.dfy")
    (d / "statement.txt").write_text(task["description"], encoding="utf-8")
    (d / "BRIEF.md").write_text((HERE / "BRIEF.md").read_text().replace("{{DIR}}", str(d)))
    for name, text in (("fuzz", FUZZ), ("trace", TRACE)):
        (d / name).write_text(text.format(py=PY, run=HERE / "run.py", sid=sid, fuzzing=FUZZING))
        (d / name).chmod((d / name).stat().st_mode | stat.S_IXUSR)

    label = task["time_complexity_inferred"]
    for f in ("row.dfy", "statement.txt"):
        text = (d / f).read_text()
        if label in text or LEAKS.search(text):
            raise SystemExit(f"{sid}: {f} may leak the label: {LEAKS.search(text) or label}")


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    if len(argv) < 2:
        raise SystemExit(__doc__)
    root = Path(argv[0]).resolve()
    if FUZZING.parents[1] in root.parents:
        raise SystemExit(f"{root} is inside the repository; stage outside it")
    tasks = {t["solution_id"]: t for t in read_jsonl(DATA / "tasks.jsonl")}
    for sid in argv[1:]:
        stage(root, sid, tasks[sid])
        print(f"staged {root / sid}")


if __name__ == "__main__":
    main()
