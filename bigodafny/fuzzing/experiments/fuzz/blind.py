"""Blind guess-only runs: set up rows for `blind-guess` agents, then grade their answers.

    python3 experiments/fuzz/blind.py setup --dir DIR --mode code|fuzz SID [SID ...]
    python3 experiments/fuzz/blind.py grade --dir DIR --out OUT

`setup` writes each row to DIR/<mode>/<sid>/: `row.dfy` (`annotate`'s output,
without the label) and `BRIEF.md` (the blocks for MODE, ending with the problem
statement). DIR gets one `prelude.dfy` that every `row.dfy` includes. DIR must
lie outside the repository; `setup` writes it to `guard-path` for `guard.py`.
A row whose files name the label aborts.

`grade` copies DIR to OUT, then writes there `summary.jsonl`, one line per row,
and `README.md`, one table.
"""
from __future__ import annotations
import argparse, json, re, shutil, subprocess, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
FUZZING = HERE.parents[1]
sys.path.insert(0, str(FUZZING.parent))
from common import DATA, PRELUDE, read_jsonl, write_jsonl            # noqa: E402
from guard import CMD, MARKER                                         # noqa: E402
from fuzz import TIME_LIMIT                                           # noqa: E402
from steptrace import BIN                                             # noqa: E402

TOOL = BIN / "DafnySteps"
LEAKS = re.compile(r"time complexity|time_complexity|label|audit|BigOBench", re.I)
MODES = ("code", "fuzz")


def find_row(sid):
    """The row's .dfy in its status directory."""
    pid = sid.split("_")[0]
    for d in sorted(FUZZING.parent.glob("solutions*")):
        if d.name != "solutions-proved" and (d / pid / f"{sid}.dfy").exists():
            return d / pid / f"{sid}.dfy"
    raise SystemExit(f"{sid}: no row")


def annotate(sid, row_dfy):
    """Write the row's step-counted Dafny to ROW_DFY, including the shared prelude."""
    p = subprocess.run([str(TOOL), "annotate", str(find_row(sid)), str(row_dfy),
                        "enable=functions,seq,arrays"], capture_output=True, text=True)
    if p.returncode:
        raise SystemExit(f"{sid}: annotate failed: {p.stderr.strip()}")
    text = re.sub(r'^include ".*prelude\.dfy"$', 'include "../../prelude.dfy"', row_dfy.read_text(),
                  count=1, flags=re.M)
    row_dfy.write_text(text)


def brief(mode, row_dir, statement):
    """BRIEF.md for one row: the blocks marked for MODE, placeholders filled."""
    text = re.sub(r"<!-- (\w+) -->\n(.*?)<!-- /\1 -->\n", lambda m: m[2] if m[1] == mode else "",
                  (HERE / "BRIEF.md").read_text(), flags=re.S)
    text = re.sub(r"\n{3,}", "\n\n", text)
    return (text.replace("{{DIR}}", str(row_dir)).replace("{{FUZZ}}", CMD)
            .replace("{{TIME_LIMIT}}", str(TIME_LIMIT))
            .replace("{{PRELUDE}}", str(row_dir.parents[1] / "prelude.dfy"))
            .replace("{{STATEMENT}}", statement))


def check_leaks(sid, label, files):
    """Abort if any of FILES ({name: text}) names the label."""
    for name, text in files.items():
        if label in text or LEAKS.search(text):
            raise SystemExit(f"{sid}: {name} may leak the label: {LEAKS.search(text) or label}")


def setup(row_dir, sid, task, mode):
    row_dir.mkdir(parents=True)
    annotate(sid, row_dir / "row.dfy")
    (row_dir / "BRIEF.md").write_text(brief(mode, row_dir, task["description"]), encoding="utf-8")
    check_leaks(sid, task["time_complexity_inferred"],
                {"row.dfy": (row_dir / "row.dfy").read_text(), "statement": task["description"]})


def effort(row_dir):
    """`fuzz` calls, calls with `--bound`, and gen.py versions, from `attempts/`."""
    headers = [t.read_text().splitlines()[:2] for t in row_dir.glob("attempts/*/table.txt")]
    return {"fuzz_calls": len(headers),
            "bound_tests": sum(h[-1].startswith("bound: ") for h in headers),
            "gen_versions": len(list(row_dir.glob("attempts/*/gen.py")))}


def grade(row_dir, label, guard_lines):
    """One summary line: the answer, the label, the match, the guard's denials, and
    for a `fuzz` row the effort."""
    try:
        answer = json.loads((row_dir / "answer.json").read_text())
    except (OSError, json.JSONDecodeError) as e:
        answer = {"class": None, "error": f"answer.json: {e}"}
    mode = row_dir.parent.name
    leaks = [line for line in guard_lines if f"/{mode}/{row_dir.name}" in line]
    return {"sid": row_dir.name, "mode": mode, "label": label, **answer,
            "match": answer.get("class") == label, "leaks": leaks,
            **(effort(row_dir) if mode == "fuzz" else {})}


def cell(row):
    """A row's answer in the run table."""
    if row is None or row["class"] is None:
        return "-"
    return row["class"] + (" ✓" if row["match"] else "") + (" (void)" if row["leaks"] else "")


def run_table(rows, labels):
    """The run's README table: label, code answer, fuzz answer, fuzz calls."""
    by_key = {(r["sid"], r["mode"]): r for r in rows}
    lines = ["| row | label | code | fuzz | fuzz calls |", "|---|---|---|---|---|"]
    for sid in dict.fromkeys(r["sid"] for r in rows):
        fuzz_row = by_key.get((sid, "fuzz"))
        calls = "-" if fuzz_row is None else f"{fuzz_row['fuzz_calls']} ({fuzz_row['bound_tests']} bound)"
        cells = [cell(by_key.get((sid, mode))) for mode in MODES] + [calls]
        lines.append(f"| `{sid}` | {labels[sid]} | " + " | ".join(cells) + " |")
    lines += ["", "✓: the class equals the label."]
    if any(r["leaks"] for r in rows):
        lines += ["(void): the guard logged a denial or a broken answer for the row."]
    return lines


def cmd_setup(root, mode, sids, tasks):
    if FUZZING.parents[1] in root.parents:
        raise SystemExit(f"{root} is inside the repository; set up outside it")
    root.mkdir(parents=True, exist_ok=True)
    shutil.copy(PRELUDE, root / "prelude.dfy")
    for sid in sids:
        setup(root / mode / sid, sid, tasks[sid], mode)
        print(f"set up {root / mode / sid}")
    MARKER.write_text(str(root))
    print(f"{MARKER} = {root}: guard.py confines agents to it")


def cmd_grade(root, out, tasks):
    labels = {sid: t["time_complexity_inferred"] for sid, t in tasks.items()}
    guard_log = root / "guard.log"
    guard_lines = guard_log.read_text().splitlines() if guard_log.exists() else []
    rows = [grade(row_dir, labels[row_dir.name], guard_lines)
            for mode in MODES for row_dir in sorted((root / mode).glob("*/"))
            if (row_dir / "BRIEF.md").exists()]
    shutil.copytree(root, out, dirs_exist_ok=True, ignore=shutil.ignore_patterns(".locks"))
    write_jsonl(out / "summary.jsonl", rows)
    lines = run_table(rows, labels)
    (out / "README.md").write_text(f"# Blind run {root.name}\n\n" + "\n".join(lines) + "\n")
    print("\n".join(lines))
    print(f"-> {out}")


def main():
    parser = argparse.ArgumentParser(prog="blind.py")
    sub = parser.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("setup", help="set up rows for agents")
    s.add_argument("--dir", required=True, type=Path, help="where to write the rows; outside the repository")
    s.add_argument("--mode", required=True, choices=MODES, help="code: read only; fuzz: also fuzz.py")
    s.add_argument("sids", nargs="+", metavar="SID")
    g = sub.add_parser("grade", help="collect answers, add labels, copy DIR to OUT")
    g.add_argument("--dir", required=True, type=Path, help="the directory setup wrote")
    g.add_argument("--out", required=True, type=Path, help="where to copy the run and write the summary")
    args = parser.parse_args()
    tasks = {t["solution_id"]: t for t in read_jsonl(DATA / "tasks.jsonl")}
    if args.cmd == "setup":
        cmd_setup(args.dir.resolve(), args.mode, args.sids, tasks)
    else:
        cmd_grade(args.dir.resolve(), args.out.resolve(), tasks)


if __name__ == "__main__":
    main()
