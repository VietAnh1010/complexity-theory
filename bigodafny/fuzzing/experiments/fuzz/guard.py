#!/usr/bin/env python3
"""PreToolUse and Stop hook of the `blind-guess` agent (`.claude/agents/blind-guess.md`).

Keeps each agent inside its row directory and keeps it from stopping without an
answer. `guard-path`, beside this file, names the stage root (`blind.py setup`
writes it); without it every call is denied.

- Only the tools in `PATHS` are allowed.
- Bash runs only `CMD DFY GEN [--per N] [--bound 'E']`, in the foreground, and
  only in a `fuzz` row.
- Every path must lie in the agent's row directory: the first one it touches.
  Read and Grep may also open the stage root's `prelude.dfy`.
- On Stop, `answer.json` must hold every key of `BRIEF.md`'s example (and
  `skipped` in a `fuzz` row), with `class` in its form. The stop is blocked
  `TRIES` times, then the hook fails.

Each denial, and a stop that fails, goes to `<stage root>/guard.log` and voids the row.
"""
from __future__ import annotations
import json, re, sys, time
from pathlib import Path

HERE = Path(__file__).resolve().parent
MARKER = HERE / "guard-path"                                           # written by blind.py setup
CMD = f"{HERE.parents[2] / '.venv' / 'bin' / 'python3'} {HERE / 'fuzz.py'}"     # BRIEF.md's {{FUZZ}}
FUZZ = re.compile(re.escape(CMD) + r" (?P<dfy>[\w./-]+\.dfy) (?P<gen>[\w./-]+/gen\.py)"
                  r"(?: --per \d+| --bound '[^'\n]*'){0,2}")
PATHS = {"Read": ["file_path"], "Write": ["file_path"], "Edit": ["file_path"],     # tool -> path arguments
         "Glob": ["path"], "Grep": ["path"], "Bash": ["dfy", "gen"],   # Bash: FUZZ's groups
         "SubagentHandback": []}                            # returns the agent's report
KEYS = ("class", "measures", "worst_case", "example", "reasoning", "confidence")
CLASS = re.compile(r"O\([0-9a-z+*().]+\)")                            # BRIEF.md: O(nlogn), O(n**1.5), ...
TRIES = 3


def row_of(path, root):
    """The row directory (holding BRIEF.md) at or above PATH, under ROOT."""
    p = Path(path).resolve()
    for d in [p, *p.parents]:
        if d == root or root not in d.parents:
            return None
        if (d / "BRIEF.md").exists():
            return d
    return None


def agent_row(root, agent):
    """The row AGENT is locked to, or None."""
    lock = root / ".locks" / str(agent)
    return Path(lock.read_text()) if lock.exists() else None


def lock_reason(agent, row, root):
    """None if AGENT may work in ROW, else why not. Locks AGENT to its first row."""
    if row is None:
        return "work inside your row directory"
    mine = agent_row(root, agent)
    if mine is None:
        (root / ".locks").mkdir(exist_ok=True)
        (root / ".locks" / str(agent)).write_text(str(row))
        return None
    return None if row == mine else f"{row} is not your directory {mine}"


def path_reason(tool, path, root, agent):
    """None if TOOL may use PATH, else why not."""
    resolved = Path(path).resolve()
    if tool in ("Read", "Grep") and resolved == root / "prelude.dfy":
        return None
    if not resolved.is_relative_to(root):
        return f"{path} is outside {root}"
    row = row_of(path, root)
    if why := lock_reason(agent, row, root):
        return why
    if tool == "Bash" and row.parent.name == "code":
        return "this mode has no Bash"
    return None


def deny_reason(tool, args, root, agent):
    """None if the call is allowed, else why not."""
    if tool not in PATHS:
        return f"{tool} is not available"
    pattern = args.get("pattern", "")
    if tool == "Glob" and (pattern.startswith("/") or ".." in pattern):
        return "give a pattern relative to `path`"
    if tool == "Bash":
        if args.get("run_in_background"):
            return "run fuzz in the foreground"
        if not (m := FUZZ.fullmatch(args.get("command", "").strip())):
            return f"Bash runs only `{CMD} DFY GEN [--per N] [--bound 'E']`"
        args = m.groupdict()
    for key in PATHS[tool]:
        if key not in args:
            return f"give `{key}` under your directory"
        if why := path_reason(tool, args[key], root, agent):
            return why
    return None


def answer_error(row):
    """None if ROW/answer.json is complete, else what is wrong."""
    if row is None:
        return "you have no row directory"
    try:
        answer = json.loads((row / "answer.json").read_text())
    except (OSError, json.JSONDecodeError) as e:
        return f"answer.json: {e}"
    keys = KEYS
    if row.parent.name == "fuzz":
        keys += ("skipped",)
    if missing := [k for k in keys if not isinstance(answer, dict) or not str(answer.get(k) or "").strip()]:
        return f"answer.json lacks {', '.join(missing)}"
    if not CLASS.fullmatch(answer["class"]):
        return f"class {answer['class']!r} is not in the form BRIEF.md gives"
    if answer["confidence"] not in ("high", "medium", "low"):
        return "confidence must be high, medium or low"
    return None


def log_denial(root, payload, why):
    with (root / "guard.log").open("a", encoding="utf-8") as fh:
        fh.write(json.dumps({"ts": time.strftime("%Y-%m-%dT%H:%M:%S"),
                             "agent": str(payload.get("agent_id"))[:24],
                             "tool": payload.get("tool_name") or payload.get("hook_event_name"), "why": why,
                             "input": json.dumps(payload.get("tool_input"))[:600]}) + "\n")


def count_stop(root, agent):
    """How many times AGENT has tried to stop, this try included."""
    counter = root / ".locks" / f"{agent}.stops"
    tries = int(counter.read_text()) + 1 if counter.exists() else 1
    counter.parent.mkdir(exist_ok=True)
    counter.write_text(str(tries))
    return tries


def stop(root, payload):
    """Let the agent stop once its answer.json is complete; block it up to TRIES times."""
    agent = payload.get("agent_id") or "unknown"
    row = agent_row(root, agent)
    if (why := answer_error(row)) is None:
        sys.exit(0)
    if count_stop(root, agent) > TRIES:
        why = f"answer.json still broken after {TRIES} tries: {why}"
        payload["tool_input"] = {"row": str(row)}                      # so grade voids the row
        log_denial(root, payload, why)
        print(f"FAILED: {why}", file=sys.stderr)
        sys.exit(1)
    print(f"Do not stop yet: {why}. Fix answer.json as BRIEF.md says.", file=sys.stderr)
    sys.exit(2)


def main():
    try:
        payload = json.load(sys.stdin)
    except Exception:
        sys.exit(0)
    if not MARKER.exists():
        print(f"DENIED: no stage root; {MARKER} is missing.", file=sys.stderr)
        sys.exit(2)
    root = Path(MARKER.read_text().strip()).resolve()
    if payload.get("hook_event_name") == "SubagentStop":
        stop(root, payload)
    why = deny_reason(payload.get("tool_name"), payload.get("tool_input") or {}, root,
                      payload.get("agent_id") or "unknown")
    if why is None:
        sys.exit(0)
    log_denial(root, payload, why)
    print(f"DENIED: {why}. Work only in your directory under {root}.", file=sys.stderr)
    sys.exit(2)


if __name__ == "__main__":
    main()
