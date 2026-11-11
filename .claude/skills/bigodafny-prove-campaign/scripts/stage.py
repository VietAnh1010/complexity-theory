#!/usr/bin/env python3
"""Stage rows for `prove-blind` agents, then audit what they wrote.

    python3 stage.py setup --batch batches/prove-hard SID [SID ...]
    python3 stage.py collect --batch batches/prove-hard --slice NAME SID [SID ...]

Run both from `bigodafny/`, with its venv's Python.

`setup` writes each row to the stage (`prove_guard.ROOT`), outside the repository:
`row.dfy` and `proof.dfy` (`annotate`'s output), `BRIEF.md` (the batch's `PROMPT.md`
with the row's label), `attempts/` and `budget.json`. The stage's `prelude.dfy` drops
the comment lines that name a row.

`collect` audits each row's best attempt, or else its last, and copies its attempts to the batch's
`attempts/`, then appends one record per row to the batch's `traj_NAME.jsonl`. The
audit is below: an attempt that fails it is not a proof, whatever the agent reported.
"""
from __future__ import annotations
import argparse, json, re, shutil, subprocess, sys, tempfile, time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from prove_guard import ROOT                                          # noqa: E402

BIGODAFNY = Path(__file__).resolve().parents[4] / "bigodafny"
sys.path.insert(0, str(BIGODAFNY))
from common import PRELUDE, read_jsonl                                # noqa: E402

ANNOTATE = BIGODAFNY / "fuzzing/DafnySteps/bin/Release/net10.0/DafnySteps"
ROW_ID = re.compile(r"(?<![\w.])\d{1,4}_\d+\b")
BANNED = re.compile(r"\bassume\b|decreases \*|\{:verify false\}|\{:axiom\}|\{:only\}")
DECL = re.compile(r"^\s*(?:ghost\s+)?(?:method|function|predicate|lemma)\b(?:\s*\{:[^}]*\})*\s+(\w+)")
VERIFIES = 3


def manifest(batch):
    return {r["solution_id"]: r for r in read_jsonl(batch / "manifest.jsonl")}


def setup(batch, sids):
    ROOT.mkdir(parents=True, exist_ok=True)
    lines = PRELUDE.read_text().splitlines(keepends=True)
    kept = [l for l in lines if not (ROW_ID.search(l) and l.lstrip().startswith("//"))]
    if any(ROW_ID.search(l) for l in kept):
        raise SystemExit("prelude still names a row outside a comment line")
    (ROOT / "prelude.dfy").write_text("".join(kept))
    rows, prompt = manifest(batch), (batch / "PROMPT.md").read_text()
    for sid in sids:
        row = ROOT / sid
        row.mkdir()
        (row / "attempts").mkdir()
        p = subprocess.run([str(ANNOTATE), "annotate", rows[sid]["path"], str(row / "row.dfy"),
                            "enable=functions,seq,arrays"], capture_output=True, text=True, cwd=BIGODAFNY)
        if p.returncode:
            raise SystemExit(f"{sid}: annotate failed: {p.stderr.strip()}")
        text = re.sub(r'^include ".*prelude\.dfy"$', 'include "../prelude.dfy"', (row / "row.dfy").read_text(),
                      count=1, flags=re.M)
        (row / "row.dfy").write_text(text)
        (row / "proof.dfy").write_text(text)
        (row / "BRIEF.md").write_text(prompt.replace("{{DIR}}", str(row)).replace("{{LABEL}}", rows[sid]["label"]))
        (row / "budget.json").write_text(json.dumps({"attempts": 0}))
        print(f"set up {row}")


def code_lines(text):
    """TEXT's stripped non-comment lines, without `include` and `decreases *`."""
    return [s for s in (l.split("//")[0].strip() for l in text.splitlines())
            if s and not s.startswith("include ") and s != "decreases *"]


def requires_by_decl(text):
    """{declaration name: its `requires` lines}."""
    found, name = {}, None
    for s in code_lines(text):
        if m := DECL.match(s):
            name = m[1]
            found.setdefault(name, [])
        elif s.startswith("requires") and name:
            found[name].append(s)
        elif s.startswith("{"):
            name = None
    return found


def emitted_python(path):
    with tempfile.TemporaryDirectory() as tmp:
        p = subprocess.run(["dafny", "translate", "py", str(path), "--no-verify", "--output", f"{tmp}/m"],
                           capture_output=True, text=True, timeout=600)
        mod = Path(f"{tmp}/m-py/module_.py")
        return mod.read_text() if p.returncode == 0 and mod.exists() else None


def best_attempt(row):
    """The attempt ROW's agent names as its proof, or None."""
    try:
        return json.loads((row / "result.json").read_text()).get("best_attempt")
    except (OSError, json.JSONDecodeError):
        return None


def audit(sid, row, repo_row):
    """The reasons ROW's best attempt, or else its last, is not a proof; [] when it is one."""
    attempts = sorted((row / "attempts").glob("*.dfy"), key=lambda p: int(p.stem))
    if not attempts:
        return ["no attempt"]
    best = row / "attempts" / f"{best_attempt(row)}.dfy"
    last, why = row / "audited.dfy", []             # beside proof.dfy, so its `include` resolves
    shutil.copy(best if best.exists() else attempts[-1], last)
    text = last.read_text()
    if m := BANNED.search(text):
        why.append(f"banned: {m[0]}")
    if not re.search(r"^\s*ensures\s+steps\s*<=", text, flags=re.M):
        why.append("no top-level `ensures steps <= E`")
    # every annotate line but an `invariant` stays, in order; the verifier checks invariants
    proof_lines = iter(code_lines(text))
    missing = [l for l in code_lines((row / "row.dfy").read_text())
               if not l.startswith("invariant") and l not in proof_lines]
    if missing:                                     # lines after the first missing one all read as missing
        why.append(f"annotate line changed or moved: {missing[0]}")
    theirs, ours = requires_by_decl((row / "row.dfy").read_text()), requires_by_decl(text)
    if changed := [n for n in theirs if ours.get(n) != theirs[n]]:
        why.append(f"`requires` changed on {changed}")
    py_row, py_proof = emitted_python(repo_row), emitted_python(last)
    if py_row is None or py_row != py_proof:
        why.append("compiled Python differs" if py_row and py_proof else "translate failed")
    for i in range(VERIFIES):
        p = subprocess.run(["dafny", "verify", str(last), "--verification-time-limit", "30"],
                           capture_output=True, text=True)
        if p.returncode:
            tail = (p.stdout + p.stderr).strip().splitlines()[-1:]
            why.append(f"verify run {i + 1} of {VERIFIES} failed: {tail}")
            break
    return why


def collect(batch, slice_name, sids):
    rows = manifest(batch)
    with (batch / f"traj_{slice_name}.jsonl").open("a", encoding="utf-8") as out:
        for sid in sids:
            row = ROOT / sid
            budget = json.loads((row / "budget.json").read_text())
            try:
                result = json.loads((row / "result.json").read_text())
            except (OSError, json.JSONDecodeError):
                result = {}
            why = audit(sid, row, BIGODAFNY / rows[sid]["path"])
            pid = sid.split("_")[0]
            dest = batch / "attempts" / pid
            dest.mkdir(parents=True, exist_ok=True)
            files = []
            kept = len(list(dest.glob(f"{sid}.*.dfy")))              # a rerun never overwrites an attempt
            for a in sorted((row / "attempts").glob("*.dfy"), key=lambda p: int(p.stem)):
                files.append(f"attempts/{pid}/{sid}.{kept + int(a.stem)}.dfy")
                text = re.sub(r'^include ".*prelude\.dfy"$', 'include "../../../../prelude.dfy"', a.read_text(),
                              count=1, flags=re.M)
                (batch / files[-1]).write_text(text)
            agent_said = result.get("outcome", "no result")
            record = {"solution_id": sid, "label": rows[sid]["label"], "on": time.strftime("%Y-%m-%d"),
                      "outcome": "proved" if agent_said == "proved" and not why else "unresolved",
                      "agent_outcome": agent_said, "audit_failures": why,
                      "best_attempt": result.get("best_attempt"),
                      "stop_reason": result.get("stop_reason"), "stop_error": budget.get("stop_error"),
                      "bound": result.get("bound"), "relation": result.get("relation"),
                      "relation_reason": result.get("relation_reason", ""),
                      "obstacle": result.get("obstacle"), "why_failed": result.get("why_failed"),
                      "reads": result.get("reads", []), "attempts_used": budget["attempts"],
                      "seconds": round(budget["ended"] - budget["started"]) if "ended" in budget else None,
                      "files": files}
            out.write(json.dumps(record, sort_keys=True) + "\n")
            print(sid, record["outcome"], f"agent said {agent_said}", why or "")


def main():
    parser = argparse.ArgumentParser(prog="stage.py")
    sub = parser.add_subparsers(dest="cmd", required=True)
    for name in ("setup", "collect"):
        s = sub.add_parser(name)
        s.add_argument("--batch", required=True, type=Path)
        s.add_argument("sids", nargs="+", metavar="SID")
        if name == "collect":
            s.add_argument("--slice", required=True)
    args = parser.parse_args()
    batch = args.batch.resolve()
    setup(batch, args.sids) if args.cmd == "setup" else collect(batch, args.slice, args.sids)


if __name__ == "__main__":
    main()
