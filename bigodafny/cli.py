#!/usr/bin/env python3
"""bigodafny -- build a Python->Dafny dataset from BigOBench.

    python3 cli.py all                 fetch, extract, signatures, scaffold, baseline, dataset
    python3 cli.py extract             download + project into tasks.jsonl
    python3 cli.py signatures          dataclass_code -> Dafny signatures
    python3 cli.py scaffold [--force]  write .dfy stubs (never clobbers a real body)
    python3 cli.py baseline            run the original Python against its own tests
    python3 cli.py validate [...]      compile .dfy and diff stdout
    python3 cli.py dataset             join everything -> dataset.jsonl + stats.json
    python3 cli.py selftest            prove the validator rejects bad translations
"""
from __future__ import annotations
import argparse, sys


def main():
    ap = argparse.ArgumentParser(prog="cli.py", description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("extract")
    sub.add_parser("signatures")
    sc = sub.add_parser("scaffold"); sc.add_argument("--force", action="store_true")
    bl = sub.add_parser("baseline"); bl.add_argument("--workers", type=int, default=8)
    va = sub.add_parser("validate")
    va.add_argument("--only", nargs="*")
    va.add_argument("--generated", action="store_true")
    va.add_argument("--per-test", type=int, default=30)
    va.add_argument("--limit", type=int)
    va.add_argument("--out-prefix", default="")
    sub.add_parser("dataset")
    sub.add_parser("selftest")
    al = sub.add_parser("all"); al.add_argument("--workers", type=int, default=8)
    a = ap.parse_args()

    if a.cmd == "extract":
        import extract; extract.extract()
    elif a.cmd == "signatures":
        import signature; signature.build()
    elif a.cmd == "scaffold":
        import scaffold; scaffold.scaffold(force=a.force)
    elif a.cmd == "baseline":
        import baseline; baseline.run(workers=a.workers)
    elif a.cmd == "validate":
        import validate
        tiers = ["public_tests", "private_tests"] + \
                (["generated_tests"] if a.generated else [])
        validate.validate(only=set(a.only) if a.only else None, tiers=tuple(tiers),
                          per_test=a.per_test, limit=a.limit, out_prefix=a.out_prefix)
    elif a.cmd == "dataset":
        import dataset; dataset.build()
    elif a.cmd == "selftest":
        import selftest; return selftest.main()
    elif a.cmd == "all":
        import extract, signature, scaffold, baseline, dataset
        extract.extract(); signature.build(); scaffold.scaffold()
        baseline.run(workers=a.workers); dataset.build()
    return 0


if __name__ == "__main__":
    sys.exit(main())
