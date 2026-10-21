#!/usr/bin/env python3
"""PreToolUse and Stop hook of the `blind-guess` agent (`.claude/agents/blind-guess.md`):
confine it to the staged rows, and keep it from stopping without an answer.

The hook runs only for that agent type, so it checks every call it sees.
`guard-path`, beside this file, holds the stage root (`blind.py setup` writes it);
without it every call is denied.

- Only the tools in `PATHS` are allowed; Bash, web tools and Agent are denied.
- Every path a call names must lie in one row directory (one holding
  `BRIEF.md`) under the stage root. Each agent is locked to the first row it
  touches, so agents in one root cannot read each other's work.
- `fuzz` (`fuzz_mcp.py`) is denied in a `code` mode row.

A denial is logged to `<stage root>/guard.log` and voids that row's result.

On Stop, the agent's `answer.json` must hold every key of `BRIEF.md`'s example,
with `class` in its form. Else the stop is blocked and the agent told why, at
most `TRIES` times; then the hook fails, and logs the row void.
"""
from __future__ import annotations
import json, re, sys, time
from pathlib import Path

MARKER = Path(__file__).resolve().parent / "guard-path"                # written by blind.py setup
FUZZ = "mcp__fuzz__fuzz"
PATHS = {"Read": ["file_path"], "Write": ["file_path"], "Edit": ["file_path"],     # tool -> path arguments
         "Glob": ["path"], "Grep": ["path"], FUZZ: ["dfy", "gen"],
         "ToolSearch": [],                                  # loads the fuzz tool's schema
         "SubagentHandback": []}                            # returns the agent's report
KEYS = ("class", "measures", "worst_case", "example", "reasoning", "confidence")
CLASS = re.compile(r"O\([0-9a-z+*()]+\)")                             # BRIEF.md: O(nlogn), O(n**2), ...
TRIES = 3


def row_of(path, root):
    """The row directory (holding BRIEF.md) at or above path, under root."""
    p = Path(path).resolve()
    for d in [p, *p.parents]:
        if d == root or root not in d.parents:
            return None
        if (d / "BRIEF.md").exists():
            return d
    return None


def locked(agent, row, root):
    """None if `agent` may work in `row`; locks it there on first use."""
    if row is None:
        return "work inside your row directory"
    lock = root / ".locks" / str(agent)
    if lock.exists():
        mine = Path(lock.read_text())
        return None if row == mine else f"{row} is not your directory {mine}"
    lock.parent.mkdir(exist_ok=True)
    lock.write_text(str(row))
    return None


def verdict(tool, args, root, agent):
    """None if allowed, else the reason."""
    if tool not in PATHS:
        return f"{tool} is not available"
    if tool == "Glob" and (args.get("pattern", "").startswith("/") or ".." in args.get("pattern", "")):
        return "give a pattern relative to `path`"
    for key in PATHS[tool]:
        if key not in args:
            return f"give `{key}` under your directory"
        if not Path(args[key]).resolve().is_relative_to(root):
            return f"{args[key]} is outside {root}"
        row = row_of(args[key], root)
        if why := locked(agent, row, root):
            return why
        if tool == FUZZ and row.parent.name == "code":
            return "this mode has no fuzz tool"
    return None


def answer_error(row):
    """None if row/answer.json is complete, else what is wrong."""
    if row is None:
        return "you have no row directory"
    try:
        a = json.loads((row / "answer.json").read_text())
    except (OSError, json.JSONDecodeError) as e:
        return f"answer.json: {e}"
    if missing := [k for k in KEYS if not isinstance(a, dict) or not str(a.get(k) or "").strip()]:
        return f"answer.json lacks {', '.join(missing)}"
    if not CLASS.fullmatch(a["class"]):
        return f"class {a['class']!r} is not in the form BRIEF.md gives"
    if a["confidence"] not in ("high", "medium", "low"):
        return "confidence must be high, medium or low"
    return None


def log(root, payload, why):
    with (root / "guard.log").open("a", encoding="utf-8") as fh:
        fh.write(json.dumps({"ts": time.strftime("%Y-%m-%dT%H:%M:%S"),
                             "agent": str(payload.get("agent_id"))[:24],
                             "tool": payload.get("tool_name") or payload.get("hook_event_name"), "why": why,
                             "input": json.dumps(payload.get("tool_input"))[:600]}) + "\n")


def stop(root, payload):
    """Block the agent's stop while its answer.json is broken, at most TRIES times."""
    agent = payload.get("agent_id") or "unknown"
    lock = root / ".locks" / str(agent)
    row = Path(lock.read_text()) if lock.exists() else None
    if (why := answer_error(row)) is None:
        sys.exit(0)
    count = root / ".locks" / f"{agent}.stops"
    tries = int(count.read_text()) + 1 if count.exists() else 1
    count.parent.mkdir(exist_ok=True)
    count.write_text(str(tries))
    if tries > TRIES:
        why = f"answer.json still broken after {TRIES} tries: {why}"
        payload["tool_input"] = {"row": str(row)}                      # so grade voids the row
        log(root, payload, why)
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
    why = verdict(payload.get("tool_name"), payload.get("tool_input") or {}, root,
                  payload.get("agent_id") or "unknown")
    if why is None:
        sys.exit(0)
    log(root, payload, why)
    print(f"DENIED: {why}. Work only in your directory under {root}.", file=sys.stderr)
    sys.exit(2)


if __name__ == "__main__":
    main()
