#!/usr/bin/env python3
"""Hook of the `arms-full` agent (`.claude/agents/arms-full.md`). The rules are in `../hook.py`."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import hook                                                           # noqa: E402

hook.main(arm="full", fuzz=True, guess_first=True, push=True)
