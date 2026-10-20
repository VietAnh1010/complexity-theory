"""Stage rows for blind agents: one directory per row, outside the repository.

    python3 experiments/fuzz/stage.py [--arm prove|code|runs] ROOT SID [SID ...]

The arm picks the brief. `prove` (default): `BRIEF.md`, guess, measure and
prove. `code`: `GUESS.md`, name the class from the code alone; no wrappers,
and the hook denies Bash. `runs`: `GUESS.md`, name the class with `fuzz` and
`trace` at hand; no proof.

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
# Fill-ins for GUESS.md, per arm.
GUESS = {
    "code": {"RULE": "- Do not run anything. Use Read, Glob and Grep; the hook denies Bash.",
             "FILES": "", "TASK": "Work from the code alone."},
    "runs": {"RULE": "- Start every Bash command with `cd {{DIR}} &&`.",
             "FILES": "| `fuzz` | `./fuzz FILE.dfy gen.py [--per N]`: runs your generator's inputs on FILE, prints a table |\n"
                      "| `trace` | `./trace FILE.dfy INPUT.txt LINE,LINE`: runs one input, logs `steps` at those source lines |",
             "TASK": """You can run the program. Write `gen.py`:
```python
GRID = [{"n": 8}, {"n": 16}, ...]       # sizes, one dict per table row
FAMILIES = {"random": f, ...}           # f(rng, **sizes) -> input text, as on stdin
```
Stay inside the statement's limits. `./fuzz row.dfy gen.py` prints, per grid row, the
costliest input's `steps` and how often the busiest loops ran. To test a candidate bound E,
copy `row.dfy` to `round-k.dfy`, add `ensures steps <= E` to `Solve`, and run
`./fuzz round-k.dfy gen.py`: it also prints E and `steps / E`. A ratio that falls as sizes grow
means E is a looser class than the code; a flat ratio means the class fits; `BOUND BROKEN`
means E is too low. Write families for the inputs you think cost most, not only random ones.
Run `./fuzz` at least once and at most 3 times, and base your answer on what it shows as well as on the code."""},
}


def find_row(sid):
    pid = sid.split("_")[0]
    for d in sorted(FUZZING.parent.glob("solutions*")):
        if d.name != "solutions-proved" and (d / pid / f"{sid}.dfy").exists():
            return d / pid / f"{sid}.dfy"
    raise SystemExit(f"{sid}: no row")


def stage(root, sid, task, arm="prove"):
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
    brief = (HERE / ("BRIEF.md" if arm == "prove" else "GUESS.md")).read_text()
    for key, text in GUESS.get(arm, {}).items():
        brief = brief.replace("{{" + key + "}}", text)
    (d / "BRIEF.md").write_text(brief.replace("{{DIR}}", str(d)))
    for name, text in (("fuzz", FUZZ), ("trace", TRACE)) if arm != "code" else ():
        (d / name).write_text(text.format(py=PY, run=HERE / "run.py", sid=sid, fuzzing=FUZZING))
        (d / name).chmod((d / name).stat().st_mode | stat.S_IXUSR)

    label = task["time_complexity_inferred"]
    for f in ("row.dfy", "statement.txt"):
        text = (d / f).read_text()
        if label in text or LEAKS.search(text):
            raise SystemExit(f"{sid}: {f} may leak the label: {LEAKS.search(text) or label}")


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    arm = "prove"
    if argv[:1] == ["--arm"]:
        arm, argv = argv[1], argv[2:]
    if arm not in ("prove", "code", "runs") or len(argv) < 2:
        raise SystemExit(__doc__)
    root = Path(argv[0]).resolve()
    if FUZZING.parents[1] in root.parents:
        raise SystemExit(f"{root} is inside the repository; stage outside it")
    tasks = {t["solution_id"]: t for t in read_jsonl(DATA / "tasks.jsonl")}
    for sid in argv[1:]:
        stage(root, sid, tasks[sid], arm)
        print(f"staged {root / sid}")


if __name__ == "__main__":
    main()
