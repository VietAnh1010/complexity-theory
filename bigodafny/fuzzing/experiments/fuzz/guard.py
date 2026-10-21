#!/usr/bin/env python3
"""PreToolUse hook of the `blind-guess` agent (`.claude/agents/blind-guess.md`):
confine it to the staged rows.

The hook runs only for that agent type, so it checks every call it sees.
`guard-path`, beside this file, holds the stage root (`blind.py setup` writes it);
without it every call is denied.

- Only the tools in `PATHS` are allowed; Bash, web tools and Agent are denied.
- Every path a call names must lie in one row directory (one holding
  `BRIEF.md`) under the stage root. Each agent is locked to the first row it
  touches, so agents in one root cannot read each other's work.
- `fuzz` (`fuzz_mcp.py`) is denied in a `code` mode row.

A denial is logged to `<stage root>/guard.log` and voids that row's result.
"""
from __future__ import annotations
import json, sys, time
from pathlib import Path

MARKER = Path(__file__).resolve().parent / "guard-path"                # written by blind.py setup
FUZZ = "mcp__fuzz__fuzz"
PATHS = {"Read": ["file_path"], "Write": ["file_path"], "Edit": ["file_path"],     # tool -> path arguments
         "Glob": ["path"], "Grep": ["path"], FUZZ: ["dfy", "gen"],
         "ToolSearch": [],                                  # loads the fuzz tool's schema
         "SubagentHandback": []}                            # returns the agent's report


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


def main():
    try:
        payload = json.load(sys.stdin)
    except Exception:
        sys.exit(0)
    if not MARKER.exists():
        print(f"DENIED: no stage root; {MARKER} is missing.", file=sys.stderr)
        sys.exit(2)
    root = Path(MARKER.read_text().strip()).resolve()
    why = verdict(payload.get("tool_name"), payload.get("tool_input") or {}, root,
                  payload.get("agent_id") or "unknown")
    if why is None:
        sys.exit(0)
    with (root / "guard.log").open("a", encoding="utf-8") as fh:
        fh.write(json.dumps({"ts": time.strftime("%Y-%m-%dT%H:%M:%S"),
                             "agent": str(payload.get("agent_id"))[:24],
                             "tool": payload.get("tool_name"), "why": why,
                             "input": json.dumps(payload.get("tool_input"))[:600]}) + "\n")
    print(f"DENIED: {why}. Work only in your directory under {root}.", file=sys.stderr)
    sys.exit(2)


if __name__ == "__main__":
    main()
