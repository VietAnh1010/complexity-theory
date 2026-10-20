#!/usr/bin/env python3
"""PreToolUse hook of the `blind-fuzz` agent (`.claude/agents/blind-fuzz.md`):
confine it to the staged rows.

The hook runs only for that agent type, so it checks every call it sees.
`bigodafny/out/fuzz-confined` holds the stage root (`stage.py`); without it
every call is denied.

- File tools (Read, Write, Edit, Glob, Grep, NotebookEdit): every path must lie
  under the stage root.
- Bash: the command must start with `cd <stage root>/...`; after that it may not
  use an absolute path, `cd` again, `..`, `~`, `$HOME`, git, or name the
  repository or a label-bearing file.
- Web tools and Agent: denied.

A denial is logged to `<stage root>/guard.log` and voids that row's result.
"""
from __future__ import annotations
import json, re, sys, time
from pathlib import Path

REPO = Path(__file__).resolve().parents[4]
MARKER = REPO / "bigodafny" / "out" / "fuzz-confined"
BANNED = re.compile(r"complexity-theory|bigodafny|solutions|tasks\.jsonl|label|audit|"
                    r"time_complexity|\.claude|(^|[\s;&|(])git\b|\.\./|(^|[\s/])\.\.($|[\s/])|"
                    r"~|\$HOME|\$\{?CLAUDE|"
                    r"(^|[\s=<>'\"(;&|])/|\b(cd|pushd)\b")   # no absolute path, no second cd
FILE_TOOLS = {"Read", "Write", "Edit", "Glob", "Grep", "NotebookEdit"}
DENIED_TOOLS = {"WebFetch", "WebSearch", "Agent", "Task"}


def verdict(tool, args, root):
    """None if allowed, else the reason."""
    if tool in DENIED_TOOLS:
        return f"{tool} is not available"
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
    why = verdict(payload.get("tool_name"), payload.get("tool_input") or {}, root)
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
