#!/usr/bin/env python3
"""Hook of the `arms-noguess` agent (`.claude/agents/arms-noguess.md`). The rules are in `../hook.py`."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import hook                                                           # noqa: E402

hook.main(arm="noguess", fuzz=False, guess_first=False, push=True)
