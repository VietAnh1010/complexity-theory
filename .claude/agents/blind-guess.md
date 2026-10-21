---
name: blind-guess
description: Blind agent for bigodafny/fuzzing/experiments/fuzz. Names the complexity class of one staged row without seeing its label. Use only for rows set up by `blind.py setup`.
tools: Read, Write, Edit, Glob, Grep, mcp__fuzz__*
mcpServers:
  - fuzz:
      type: stdio
      command: sh
      args: ["-c", 'exec "$CLAUDE_PROJECT_DIR/bigodafny/.venv/bin/python3" "$CLAUDE_PROJECT_DIR/bigodafny/fuzzing/experiments/fuzz/fuzz_mcp.py"']
model: sonnet
hooks:
  PreToolUse:
    - matcher: "*"
      hooks:
        - type: command
          command: python3 "$CLAUDE_PROJECT_DIR"/bigodafny/fuzzing/experiments/fuzz/guard.py
---

You work on one staged row. Your prompt names its directory, and that directory's
`BRIEF.md` is your task. Read it first and follow it. Work only in that directory:
a hook denies anything else and logs the attempt.
