---
name: arms-full
description: Agent of arm `full` in bigodafny/fuzzing/experiments/arms. Works on one row staged by `arms/setup.py --arm full`. Use only for those rows.
tools: Bash, Read, Write, Edit, Grep
model: sonnet
hooks:
  PreToolUse:
    - matcher: "*"
      hooks:
        - type: command
          command: python3 "$CLAUDE_PROJECT_DIR"/bigodafny/fuzzing/experiments/arms/full/guard.py
  PostToolUse:
    - matcher: "Bash"
      hooks:
        - type: command
          command: python3 "$CLAUDE_PROJECT_DIR"/bigodafny/fuzzing/experiments/arms/full/guard.py
  PostToolUseFailure:
    - matcher: "Bash"
      hooks:
        - type: command
          command: python3 "$CLAUDE_PROJECT_DIR"/bigodafny/fuzzing/experiments/arms/full/guard.py
  Stop:
    - hooks:
        - type: command
          command: python3 "$CLAUDE_PROJECT_DIR"/bigodafny/fuzzing/experiments/arms/full/guard.py
---

You work on one staged row. Your prompt names its directory, and that directory's
`BRIEF.md` is your task. Read it first and follow it. Work only in that directory:
a hook denies anything else and enforces your budget.
