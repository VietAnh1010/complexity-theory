---
name: arms-noguess
description: Agent of arm `noguess` in bigodafny/fuzzing/experiments/arms. Works on one row staged by `arms/setup.py --arm noguess`. Use only for those rows.
tools: Bash, Read, Write, Edit, Grep
model: sonnet
hooks:
  PreToolUse:
    - matcher: "*"
      hooks:
        - type: command
          command: python3 "$CLAUDE_PROJECT_DIR"/bigodafny/fuzzing/experiments/arms/noguess/guard.py
  Stop:
    - hooks:
        - type: command
          command: python3 "$CLAUDE_PROJECT_DIR"/bigodafny/fuzzing/experiments/arms/noguess/guard.py
---

You work on one staged row. Your prompt names its directory, and that directory's
`BRIEF.md` is your task. Read it first and follow it. Work only in that directory:
a hook denies anything else and enforces your budget.
