#!/usr/bin/env python3
"""Is a failing gate result the translation's fault, or the harness's?

`validate.py` cannot answer that. It marshals a test's input through the
problem's own `Input.from_str`, hands the fields to the Dafny, and compares
stdout. When the result is `fail`, three things could be wrong: the Dafny, the
stored test, or the dataclass that stands between them.

This runs the ORIGINAL PYTHON through the same dataclass round-trip. It is the
control the gate does not have:

  unparseable  `Input.from_str` raised on the stored input. Neither
               implementation can be run on that test, so it is evidence about
               nothing.
  python-fails the round-trip parsed, but the original Python no longer
               reproduces the stored output from it. The dataclass lost
               information the solution needs; again not the translation's
               fault.
  python-ok    the test survives the round-trip. A Dafny failure here is a
               real translation defect.

Reads only. It never touches a gate, a record, or a translation.

    python3 batches/gate-audit/control.py 1196_100 1578_481 ...
"""

import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent.parent.parent
TASKS = HERE / "data/tasks.jsonl"


def main(argv):
    want = set(argv)
    out = []
    for line in TASKS.open():
        row = json.loads(line)
        sid = row.get("solution_id")
        if sid not in want:
            continue
        tally = {"python-ok": 0, "python-fails": 0, "unparseable": 0}
        detail = []
        for tier in ("public_tests", "private_tests"):
            for k, t in enumerate(row["tests"][tier]):
                try:
                    ns = {}
                    exec(row["dataclass_code"], ns)
                    round_trip = repr(ns["Input"].from_str(t["input"]))
                except Exception as exc:
                    tally["unparseable"] += 1
                    detail.append({"tier": tier, "i": k, "verdict": "unparseable",
                                   "error": f"{type(exc).__name__}: {exc}"[:120]})
                    continue
                p = subprocess.run([sys.executable, "-c", row["solution_code"]],
                                   input=round_trip, capture_output=True,
                                   text=True, timeout=60)
                if p.stdout == t["output"]:
                    tally["python-ok"] += 1
                else:
                    tally["python-fails"] += 1
                    detail.append({"tier": tier, "i": k, "verdict": "python-fails",
                                   "round_trip": round_trip[:80],
                                   "stored_input": t["input"][:80]})
        out.append({"solution_id": sid, "tests": sum(tally.values()),
                    **tally, "detail": detail})
        print(f"{sid:10} ok {tally['python-ok']:3}  "
              f"python-fails {tally['python-fails']:3}  "
              f"unparseable {tally['unparseable']:3}")
    (Path(__file__).resolve().parent / "control.jsonl").write_text(
        "".join(json.dumps(r) + "\n" for r in out))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
