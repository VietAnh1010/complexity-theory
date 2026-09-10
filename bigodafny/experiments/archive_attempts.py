"""Copy the blind arm's proof attempts out of the run directory into the repo.

The staged corpora live under a per-session scratch path, so every blind
`task.dfy` -- the actual artifact the experiment produces -- dies with the
container. `graded.jsonl` survives and records the verdict and the bound, but
not the proof. This lifts the proofs into `solution-guessed-verified/` so they
are committed with everything else.

Why a separate script, and why the agents do not write here themselves.

The blind arm is confined by `guard.py` to its own example directory: any tool
call reaching a repo path is denied and logged, and an example whose agent
attempted one is thrown out of the results. That containment is what makes the
blind arm's accuracy mean anything -- the label is in plain text all over this
repository. So the agent cannot be told to write here, and `grade.py` must keep
reading `task.dfy` where it is. Archiving is a step AFTER grading, run by the
main session, which is not confined and is not what is being measured.

The name mirrors `solutions-verified/`, and the distinction is the point:

    solutions-verified/        a bound proved against a KNOWN label
    solution-guessed-verified/ a bound proved against a class the agent
                               committed to in writing, before proving,
                               without ever seeing the label

Each file keeps its agent's prediction, proved bound and verdict in the header,
so the archive is readable on its own without joining back to `graded.jsonl`.
"""
from __future__ import annotations
import argparse, json, re, sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from common import ROOT, log                                      # noqa: E402

HERE = Path(__file__).resolve().parent
RUNS = HERE / "runs"
CX_ROOT = Path("/tmp/claude-0/-home-user-complexity-theory/"
               "ed2768b2-16e6-58fb-a2f9-5d0137f30fef/scratchpad/cx-run")
GUESSED = ROOT / "solution-guessed-verified"


def header(rec, res, run_id, sid, pid, include_rewritten=0):
    """Provenance block. Everything a reader needs without graded.jsonl."""
    def f(x):
        return "unavailable" if x in (None, "", []) else x
    lines = [
        f"// {sid} (problem {pid}) -- blind-arm attempt, run {run_id}",
        f"//",
        f"// The agent that wrote this never saw the complexity label. It",
        f"// committed to a class in writing before attempting the proof.",
        f"//",
        f"//   predicted class : {f(res.get('guess'))}",
        f"//   proved bound    : {f(rec.get('bound_ensures'))}",
        f"//   proved class    : {f(rec.get('bound_class'))}",
        f"//   agent verdict   : {f(res.get('verdict'))}",
        f"//   reference label : {f(rec.get('label'))}",
        f"//   prediction correct against the label: {f(rec.get('guess_correct'))}",
        f"//   all gates passed: {f(rec.get('gate_all'))}",
        f"//",
        f"// A prediction scored incorrect is not necessarily a misreading: the",
        f"// label was measured on the Python and this is the Dafny, and where",
        f"// the translation changes the class the two disagree by construction.",
        f"//",
        f"//   basis for the prediction:",
    ]
    basis = (res.get("guess_basis") or "unavailable").strip()
    for ln in _wrap(basis):
        lines.append(f"//     {ln}")
    notes = (res.get("notes") or "").strip()
    if notes:
        lines.append("//")
        lines.append("//   agent notes:")
        for ln in _wrap(notes):
            lines.append(f"//     {ln}")
    if include_rewritten:
        lines.append("//")
        lines.append("//   verbatim as the agent wrote it, except the prelude include,")
        lines.append("//   rewritten to ../../prelude.dfy so this file verifies here.")
    lines.append("// " + "-" * 68)
    return "\n".join(lines) + "\n\n"


def _wrap(text, width=70):
    out, cur = [], ""
    for word in text.split():
        if len(cur) + len(word) + 1 > width:
            out.append(cur); cur = word
        else:
            cur = f"{cur} {word}".strip()
    if cur:
        out.append(cur)
    return out or ["unavailable"]


def run(run_id, only=None, arm="blind"):
    graded_p = RUNS / run_id / "graded.jsonl"
    if not graded_p.exists():
        log(f"no graded.jsonl for run {run_id}")
        return []
    graded = [json.loads(l) for l in graded_p.read_text(encoding="utf-8").splitlines() if l.strip()]
    rows = [g for g in graded if g["arm"] == arm and (not only or g["sid"] in only)]

    written, skipped = [], 0
    for g in rows:
        sid, pid = g["sid"], g["problem_id"]
        d = CX_ROOT / run_id / arm / sid
        src, orig = d / "task.dfy", d / ".original.dfy"
        if not src.exists():
            skipped += 1
            continue
        # An untouched file is the staged original, not an attempt. Archiving it
        # would fill the directory with copies of solutions/ under a name that
        # claims a blind agent proved something.
        if orig.exists() and src.read_bytes() == orig.read_bytes():
            log(f"  {sid:>10}  skipped -- task.dfy never modified")
            skipped += 1
            continue
        res = {}
        if (d / "result.json").exists():
            try:
                res = json.loads((d / "result.json").read_text(encoding="utf-8"))
            except json.JSONDecodeError:
                res = {}
        # The staged example keeps prelude.dfy beside task.dfy; the repo keeps
        # one at the root. Rewriting the include is the ONLY edit made to an
        # agent's file, and without it the archive would not verify in place --
        # which would make it a record of a proof rather than a proof.
        body = src.read_text(encoding="utf-8")
        body, n = re.subn(r'include\s+"prelude\.dfy"',
                          'include "../../prelude.dfy"', body)
        dst = GUESSED / pid / f"{sid}.dfy"
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.write_text(header(g, res, run_id, sid, pid, include_rewritten=n)
                       + body, encoding="utf-8")
        written.append(str(dst.relative_to(ROOT)))
        log(f"  {sid:>10}  -> {dst.relative_to(ROOT)}  "
            f"(guess={res.get('guess')} proved={g.get('bound_class')})")

    log(f"archived {len(written)} blind attempt(s); {skipped} skipped")
    return written


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--run-id", required=True)
    ap.add_argument("--only", nargs="*")
    ap.add_argument("--arm", default="blind", choices=["blind", "labeled"])
    a = ap.parse_args()
    run(a.run_id, a.only, a.arm)
