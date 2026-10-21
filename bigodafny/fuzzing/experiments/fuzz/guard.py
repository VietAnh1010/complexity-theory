#!/usr/bin/env python3
"""PreToolUse hook of the `blind-guess` agent (`.claude/agents/blind-guess.md`):
confine it to the staged rows.

The hook runs only for that agent type, so it checks every call it sees.
`guard-path`, beside this file, holds the stage root (`blind.py setup` writes it);
without it every call is denied.

- File tools (Read, Write, Edit, Glob, Grep, NotebookEdit): every path must lie
  under the stage root.
- Bash: the command must start with `cd <stage root>/...`; after that it may not
  use an absolute path, `cd` again, `..`, `~`, `$HOME`, git, or name the
  repository or a label-bearing file.
- Web tools and Agent: denied.
- Each agent is locked to the first row directory (one holding `BRIEF.md`) it
  touches, so agents in one root cannot read each other's work. In a row with
  no `fuzz` wrapper (the `code` mode) Bash is denied.

A denial is logged to `<stage root>/guard.log` and voids that row's result.
"""
from __future__ import annotations
import json, re, sys, time
from pathlib import Path

MARKER = Path(__file__).resolve().parent / "guard-path"                # written by blind.py setup
BANNED = re.compile(r"complexity-theory|bigodafny|solutions|tasks\.jsonl|label|audit|"
                    r"time_complexity|\.claude|(^|[\s;&|(])git\b|\.\./|/\.\.|"
                    r"(^|[\s=<>'\"(;&|])~\w*/|\$HOME|\$\{?CLAUDE|"
                    r"(^|[\s=<>'\"(;&|])/(?!dev/null)[\w.-]+/|\b(cd|pushd)\b")   # no absolute path, no second cd
FILE_TOOLS = {"Read", "Write", "Edit", "Glob", "Grep", "NotebookEdit"}
DENIED_TOOLS = {"WebFetch", "WebSearch", "Agent", "Task"}


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


def verdict(tool, args, root, agent=None):
    """None if allowed, else the reason."""
    if tool in DENIED_TOOLS:
        return f"{tool} is not available"
    if agent is not None and tool in FILE_TOOLS | {"Bash"}:
        target = (args.get("file_path") or args.get("path") or args.get("notebook_path") if tool != "Bash"
                  else args.get("command", "").strip()[3:].split(" ")[0].split(";")[0])
        row = row_of(target, root) if target else None
        if why := locked(agent, row, root):
            return why
        if tool == "Bash" and not (row / "fuzz").exists():
            return "this mode has no Bash; use Read, Glob and Grep"
    if tool in FILE_TOOLS:
        for key in ("file_path", "path", "notebook_path"):
            if key in args and not Path(args[key]).resolve().is_relative_to(root):
                return f"{args[key]} is outside {root}"
        if tool in ("Glob", "Grep") and "path" not in args:
            return "give `path` under your directory"
        return None
    if tool == "Bash":
        cmd = args.get("command", "").strip()
        if not cmd.startswith(f"cd {root}/"):
            return f"start the command with `cd {root}/<your row> &&`"
        rest = cmd[len(f"cd {root}/"):].replace(str(root), "ROOT")   # the root's own path may match
        if m := BANNED.search(rest):
            return f"the command names {m.group(0)!r}"
        return None
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
