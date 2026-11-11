#!/usr/bin/env python3
"""Hook of the `arms-nofuzz` agent (`.claude/agents/arms-nofuzz.md`). The rules are in `../hook.py`."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import hook                                                           # noqa: E402

hook.main(arm="nofuzz", fuzz=False, guess_first=True, push=True)
