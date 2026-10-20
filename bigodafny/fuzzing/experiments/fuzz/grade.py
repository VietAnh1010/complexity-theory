"""Grade a blind run: check each row's claims against the verifier, then copy the run out.

    python3 experiments/fuzz/grade.py ROOT OUT

For each staged row in ROOT (`stage.py`):

- `proof`: the proof `record.json` names, else the newest `verify-<n>.dfy`;
  `verified` only if `dafny verify` reports 0 errors and the file has no
  `assume`, `{:axiom}` or `decreases *`.
- `same_code`: the proof compiles to the same Python as `row.dfy`, so the
  proof added only ghost code.
- `leaks`: lines of `ROOT/guard.log` naming the row, and file access in the
  agent's `gen.py`. Either voids the row.
- `label`: BigOBench's label, joined only here, after the agent finished.

Writes OUT/summary.jsonl and OUT/README.md, and copies each row's directory
to OUT/<sid>/ (generated Python and build output left out).
"""
from __future__ import annotations
import json, re, shutil, subprocess, sys, tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[2]))
from common import DATA, read_jsonl, write_jsonl                     # noqa: E402

UNSOUND = re.compile(r"\bassume\b|\{:axiom\}|decreases \*")
FILE_ACCESS = re.compile(r"\bopen\(|\bos\.|pathlib|subprocess|\bglob\b|__import__|importlib")


def verifies(f):
    p = subprocess.run(["dafny", "verify", f.name], cwd=f.parent, capture_output=True,
                       text=True, timeout=900)
    last = (p.stdout.strip().splitlines() or [""])[-1]
    return p.returncode == 0 and " 0 errors" in last, last


def python_of(f):
    """The Python `dafny translate py` emits for f's own module."""
    with tempfile.TemporaryDirectory() as d:
        p = subprocess.run(["dafny", "translate", "py", f.name, "--no-verify",
                            "--output", f"{d}/out"], cwd=f.parent, capture_output=True,
                           text=True, timeout=300)
        mod = Path(d) / "out-py" / "module_.py"
        return mod.read_text() if p.returncode == 0 and mod.exists() else None


def grade(d, label, guard_lines):
    rec = {}
    if (d / "record.json").exists():
        try:
            rec = json.loads((d / "record.json").read_text())
        except json.JSONDecodeError as e:
            rec = {"unparsed": str(e)}
    attempts = sorted(d.glob("verify-*.dfy"), key=lambda f: int(re.sub(r"\D", "", f.stem) or 0))
    named = (rec.get("proof") or {}).get("file")
    proof = d / named if named and (d / named).exists() else (attempts[-1] if attempts else None)
    out = {"sid": d.name, "label": label, "agent": rec, "attempts": len(attempts),
           "rounds": len(list(d.glob("round-*.dfy")))}
    if proof:
        ok, last = verifies(proof)
        unsound = bool(UNSOUND.search(proof.read_text()))
        out.update(proof=proof.name, verify=last, verified=ok and not unsound,
                   unsound=unsound, same_code=python_of(proof) == python_of(d / "row.dfy"))
    gen = (d / "gen.py").read_text() if (d / "gen.py").exists() else ""
    out["leaks"] = [l for l in guard_lines if f"/{d.name}" in l] + \
        [f"gen.py: {m.group(0)}" for m in FILE_ACCESS.finditer(gen)]
    return out


def main(argv=None):
    root, dest = (Path(a).resolve() for a in (argv or sys.argv[1:]))
    labels = {t["solution_id"]: t["time_complexity_inferred"] for t in read_jsonl(DATA / "tasks.jsonl")}
    guard = (root / "guard.log").read_text().splitlines() if (root / "guard.log").exists() else []
    rows = [grade(d, labels[d.name], guard) for d in sorted(root.iterdir())
            if d.is_dir() and (d / "BRIEF.md").exists()]
    dest.mkdir(parents=True, exist_ok=True)
    for r in rows:
        shutil.copytree(root / r["sid"], dest / r["sid"], dirs_exist_ok=True,
                        ignore=shutil.ignore_patterns("*-py", "__pycache__", "fuzz", "trace"))
    if guard:
        shutil.copy(root / "guard.log", dest / "guard.log")
    write_jsonl(dest / "summary.jsonl", rows)

    def cls(r, k):
        return (r["agent"].get(k) or {}).get("class", "-") if isinstance(r["agent"].get(k), dict) else "-"
    lines = ["| row | label | guess (code) | measured | proved | verified | same code | leaks |",
             "|---|---|---|---|---|---|---|---|"]
    for r in rows:
        lines.append(f"| `{r['sid']}` | {r['label']} | {cls(r, 'g0')} | {cls(r, 'final')} | "
                     f"{cls(r, 'proof')} | {r.get('verified', '-')} | {r.get('same_code', '-')} | "
                     f"{len(r['leaks'])} |")
    unattributed = [l for l in guard if not any(f"/{r['sid']}" in l for r in rows)]
    (dest / "README.md").write_text(
        f"# Blind run: {root.name}\n\nRows staged by `stage.py`, run by `blind-fuzz` agents, "
        "graded by `grade.py`.\nThe label was joined after the agents finished.\n\n"
        + "\n".join(lines) + "\n\n"
        + f"Guard denials not tied to a row: {len(unattributed)}.\n")
    print("\n".join(lines))
    print(f"-> {dest}")


if __name__ == "__main__":
    main()
