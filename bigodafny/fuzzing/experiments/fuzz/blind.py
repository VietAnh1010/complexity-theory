"""Blind guess-only runs: set up rows for `blind-guess` agents, then grade their answers.

    python3 experiments/fuzz/blind.py setup --dir DIR --mode code|fuzz SID [SID ...]
    python3 experiments/fuzz/blind.py grade --dir DIR --out OUT

`setup` writes DIR/<mode>/<sid>/ and writes DIR to `guard-path`, where
`guard.py` reads it. DIR must lie outside the repository. Each row gets
`annotate`'s output as `row.dfy` (no label) and `BRIEF.md`, which ends with
the problem statement; DIR gets one `prelude.dfy` that every `row.dfy` includes. The mode only picks the blocks of `BRIEF.md`;
`guard.py` denies Bash, which runs only `fuzz.py`, in `code` mode. A file naming the
label aborts.

`grade` copies DIR to OUT and writes there `summary.jsonl`, one line per row,
and `README.md`, one table.
"""
from __future__ import annotations
import argparse, json, re, shutil, subprocess, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
FUZZING = HERE.parents[1]
sys.path.insert(0, str(FUZZING.parent))
from common import DATA, PRELUDE, read_jsonl, write_jsonl            # noqa: E402
from guard import CMD                                                 # noqa: E402

MARKER = HERE / "guard-path"                                           # read by guard.py
TOOL = FUZZING / "DafnySteps" / "bin" / "Release" / "net10.0" / "DafnySteps"
LEAKS = re.compile(r"time complexity|time_complexity|label|audit|BigOBench", re.I)
MODES = ("code", "fuzz")


def find_row(sid):
    pid = sid.split("_")[0]
    for d in sorted(FUZZING.parent.glob("solutions*")):
        if d.name != "solutions-proved" and (d / pid / f"{sid}.dfy").exists():
            return d / pid / f"{sid}.dfy"
    raise SystemExit(f"{sid}: no row")


def setup(d, sid, task, mode):
    d.mkdir(parents=True)
    p = subprocess.run([str(TOOL), "annotate", str(find_row(sid)), str(d / "row.dfy"),
                        "enable=functions,seq,arrays"], capture_output=True, text=True)
    if p.returncode:
        raise SystemExit(f"{sid}: annotate failed: {p.stderr.strip()}")
    row = (d / "row.dfy").read_text()
    row = re.sub(r'^include ".*prelude\.dfy"$', 'include "../../prelude.dfy"', row, count=1, flags=re.M)
    (d / "row.dfy").write_text(row)
    # Keep the blocks marked for this mode, drop the others.
    brief = re.sub(r"<!-- (\w+) -->\n(.*?)<!-- /\1 -->\n", lambda m: m[2] if m[1] == mode else "",
                   (HERE / "BRIEF.md").read_text(), flags=re.S)
    brief = re.sub(r"\n{3,}", "\n\n", brief)
    (d / "BRIEF.md").write_text(brief.replace("{{DIR}}", str(d)).replace("{{FUZZ}}", CMD)
                                .replace("{{PRELUDE}}", str(d.parents[1] / "prelude.dfy"))
                                .replace("{{STATEMENT}}", task["description"]), encoding="utf-8")

    label = task["time_complexity_inferred"]
    for f, text in (("row.dfy", (d / "row.dfy").read_text()), ("statement", task["description"])):
        if label in text or LEAKS.search(text):
            raise SystemExit(f"{sid}: {f} may leak the label: {LEAKS.search(text) or label}")


def grade(d, label, guard):
    try:
        answer = json.loads((d / "answer.json").read_text())
    except (OSError, json.JSONDecodeError) as e:
        answer = {"class": None, "error": f"answer.json: {e}"}
    leaks = [l for l in guard if f"/{d.parent.name}/{d.name}" in l]
    return {"sid": d.name, "mode": d.parent.name, "label": label, **answer,
            "match": answer.get("class") == label, "leaks": leaks}


def main(argv=None):
    ap = argparse.ArgumentParser(prog="blind.py")
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("setup", help="set up rows for agents")
    s.add_argument("--dir", required=True, type=Path, help="where to write the rows; outside the repository")
    s.add_argument("--mode", required=True, choices=MODES, help="code: read only; fuzz: also fuzz.py")
    s.add_argument("sids", nargs="+", metavar="SID")
    g = sub.add_parser("grade", help="collect answers, add labels, copy DIR to OUT")
    g.add_argument("--dir", required=True, type=Path, help="the directory setup wrote")
    g.add_argument("--out", required=True, type=Path, help="where to copy the run and write the summary")
    a = ap.parse_args(argv)
    tasks = {t["solution_id"]: t for t in read_jsonl(DATA / "tasks.jsonl")}
    root = a.dir.resolve()

    if a.cmd == "setup":
        if FUZZING.parents[1] in root.parents:
            raise SystemExit(f"{root} is inside the repository; set up outside it")
        root.mkdir(parents=True, exist_ok=True)
        shutil.copy(PRELUDE, root / "prelude.dfy")
        for sid in a.sids:
            setup(root / a.mode / sid, sid, tasks[sid], a.mode)
            print(f"set up {root / a.mode / sid}")
        MARKER.write_text(str(root))
        print(f"{MARKER} = {root}: guard.py confines agents to it")
        return

    dest = a.out.resolve()
    guard = (root / "guard.log").read_text().splitlines() if (root / "guard.log").exists() else []
    rows = [grade(d, tasks[d.name]["time_complexity_inferred"], guard)
            for mode in MODES for d in sorted((root / mode).glob("*/")) if (d / "BRIEF.md").exists()]
    shutil.copytree(root, dest, dirs_exist_ok=True,
                    ignore=shutil.ignore_patterns(".locks"))
    write_jsonl(dest / "summary.jsonl", rows)
    by = {(r["sid"], r["mode"]): r for r in rows}
    lines = ["| row | label | code | fuzz |", "|---|---|---|---|"]
    for sid in dict.fromkeys(r["sid"] for r in rows):
        cells = []
        for mode in MODES:
            r = by.get((sid, mode))
            cells.append("-" if r is None or r["class"] is None else
                         r["class"] + (" ✓" if r["match"] else "") + (" (void)" if r["leaks"] else ""))
        lines.append(f"| `{sid}` | {tasks[sid]['time_complexity_inferred']} | " + " | ".join(cells) + " |")
    lines += ["", "✓: the class equals the label."]
    if any(r["leaks"] for r in rows):
        lines += ["(void): the guard logged a denial or a broken answer for the row."]
    (dest / "README.md").write_text(f"# Blind run {root.name}\n\n" + "\n".join(lines) + "\n")
    print("\n".join(lines))
    print(f"-> {dest}")


if __name__ == "__main__":
    main()
