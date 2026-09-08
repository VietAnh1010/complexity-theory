#!/usr/bin/env python3
"""PreToolUse hook: confine experiment agents to their own example directory.

Prevention, where `harvest.py` is detection. The label is not hidden in this
repository -- all 506 files in `solutions/` carry `// time complexity: O(...)`
in their header, and `data/`, `COMPLEXITY.md`, `summaries/`, the skills and
`git log` all carry it too. A blind agent left loose in the tree can read the
answer in one call, and the accuracy number would then be measuring nothing.

Active only while a marker file exists:

    experiments/runs/<run-id>/AGENTS_CONFINED

With no marker the hook exits 0 immediately, so it costs nothing between runs.
While the marker is present, any **subagent** tool call touching the repository
or naming a label-bearing artefact is denied and logged. The main session is
not confined: it has to read the repo to grade, and it is not the thing being
measured.

Two deliberate choices:

  * fail closed. If the payload does not identify the caller, it is treated as
    a subagent. A hook that fails open under an unfamiliar payload is not a
    control.
  * both arms are confined, not just the blind one. Confining only the blind
    arm would make containment itself a difference between the arms.

Every denial is appended to `runs/<run-id>/guard.log`. Attempts are a result in
their own right: a run with attempts is a run whose accuracy carries an
asterisk, whether or not the attempt succeeded.
"""
from __future__ import annotations
import json, re, sys, time
from pathlib import Path

HERE = Path(__file__).resolve().parent
RUNS = HERE / "runs"
MARKER = "AGENTS_CONFINED"

BANNED = [
    (re.compile(r"solutions(-[a-z]+)?/"), "the repo solutions tree"),
    (re.compile(r"tasks\.jsonl|dataset\.jsonl|stats\.json|validation\.jsonl"),
     "the dataset files"),
    (re.compile(r"COMPLEXITY\.md|STATUS\.md|summaries/|CLAUDE\.md"),
     "the project notes"),
    (re.compile(r"\.claude/(skills|agents|plans)"), "the project skills"),
    (re.compile(r"\bgit\s+(log|show|diff|grep|blame|cat-file)"), "git history"),
    (re.compile(r"time_complexity"), "the label field itself"),
    (re.compile(r"/home/user/complexity-theory(?!.*cx-run)"), "the repository"),
]


def active():
    for p in sorted(RUNS.glob(f"*/{MARKER}")):
        return p.parent
    return None


def main():
    try:
        payload = json.load(sys.stdin)
    except Exception:
        sys.exit(0)                      # nothing to judge

    # Debug trace: proves whether the hook is being invoked at all, and with
    # what caller identification. Enabled by a GUARD_TRACE file next to it.
    if (HERE / "GUARD_TRACE").exists():
        with (HERE / "guard_trace.log").open("a", encoding="utf-8") as fh:
            fh.write(json.dumps({"ts": time.strftime("%H:%M:%S"),
                                 "tool": payload.get("tool_name"),
                                 "transcript": payload.get("transcript_path"),
                                 "cwd": payload.get("cwd"),
                                 "keys": sorted(payload.keys())}) + "\n")

    run = active()
    if run is None:
        sys.exit(0)

    # How a subagent is identified, determined by tracing real payloads rather
    # than assumed: a subagent's PreToolUse payload carries `agent_id` and
    # `agent_type`; the main session's does not. `transcript_path` is NOT the
    # discriminator -- it names the parent session transcript in both cases,
    # and reading it that way let a probe agent walk straight into the repo.
    agent = payload.get("agent_id") or payload.get("agent_type")
    if not agent:
        sys.exit(0)                      # the main session grades; it is not measured

    blob = json.dumps(payload.get("tool_input") or {})
    for rx, why in BANNED:
        if rx.search(blob):
            line = {"ts": time.strftime("%Y-%m-%dT%H:%M:%S"),
                    "tool": payload.get("tool_name"), "why": why,
                    "agent": str(agent)[:24],
                    "input": blob[:600]}
            with (run / "guard.log").open("a", encoding="utf-8") as fh:
                fh.write(json.dumps(line) + "\n")
            print(f"DENIED: this call reaches {why}, which is outside your "
                  f"example directory. Everything you need -- the task, the "
                  f"Dafny, the Python, the guide, the prelude -- is already in "
                  f"your working directory. Work only there.", file=sys.stderr)
            sys.exit(2)
    sys.exit(0)


if __name__ == "__main__":
    main()
