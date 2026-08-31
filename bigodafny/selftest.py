"""Prove the validator rejects bad translations, and says which kind of bad.

A validator only ever run against correct input is untested. These two fixtures
are deliberately broken, in the two ways that matter:

  wrong  -- compiles, runs, prints the wrong answer  -> must be `fail`
  broken -- Dafny will not accept it at all          -> must be `build`

If a wrong answer were reported as `build`, or a build error as `fail`, the
dataset's failure counts would be meaningless.
"""
from __future__ import annotations
import shutil, sys, tempfile
from pathlib import Path

from common import PRELUDE, SOLUTIONS, log
from validate import validate

BASE = ("5", "5_100")


def fixture(root: Path, mutate) -> Path:
    """Mirror the real tree layout: the stub's `include "../../prelude.dfy"`
    only resolves if prelude sits two levels above the .dfy."""
    pid, sid = BASE
    src = (SOLUTIONS / pid / f"{sid}.dfy").read_text(encoding="utf-8")
    shutil.copy(PRELUDE, root / "prelude.dfy")
    dst = root / "solutions" / pid
    dst.mkdir(parents=True, exist_ok=True)
    (dst / f"{sid}.dfy").write_text(mutate(src), encoding="utf-8")
    return root / "solutions"


def main() -> int:
    cases = [
        ("wrong", "fail",
         lambda s: s.replace('output := IntToString(m) + "\\n";',
                             'output := IntToString(m + 1) + "\\n";')),
        ("broken", "build",
         lambda s: s.replace("var m, k := n, 1;", "var m, k := n, ;")),
    ]
    bad = 0
    for name, want, mutate in cases:
        with tempfile.TemporaryDirectory() as d:
            sols = fixture(Path(d), mutate)
            rows = validate(only={BASE[1]}, solutions_dir=sols,
                            out_prefix=f"selftest_{name}_")
            got = rows[0]["status"] if rows else "no-rows"
            ok = got == want
            bad += not ok
            log(f"{'ok  ' if ok else 'FAIL'} fixture {name!r}: "
                f"expected {want!r}, got {got!r}")
    # And the unmutated original must still be valid, or the fixtures prove
    # nothing about the mutation.
    rows = validate(only={BASE[1]}, out_prefix="selftest_control_")
    ok = rows and rows[0]["status"] == "valid"
    bad += not ok
    log(f"{'ok  ' if ok else 'FAIL'} control: expected 'valid', "
        f"got {rows[0]['status'] if rows else 'no-rows'!r}")
    log("SELFTEST PASSED" if not bad else f"SELFTEST FAILED ({bad})")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
