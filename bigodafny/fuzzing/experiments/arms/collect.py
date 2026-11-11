"""Audit one arm's staged batch, copy it to `runs/<arm>/<batch>/`, then clear the stage.

    ../../../.venv/bin/python3 collect.py --arm full --batch 1

A trial batch replaces its earlier run; any other batch never does. The audit is `stage.audit` from the prove campaign: an attempt that fails it is not a proof,
whatever the agent reported. `runs/<arm>/<batch>/traj.jsonl` gets one record per row.
"""
from __future__ import annotations
import argparse, json, shutil
from pathlib import Path

from setup import ARMS, ARM_NAMES, BIGODAFNY, STAGE, read_jsonl
from report import TRIAL
import hook
import stage

KEPT = ("guess", "guess_basis", "class", "bound", "best_attempt", "relation", "relation_reason",
        "obstacle", "why_failed", "stop_reason")


def record(arm, batch, entry, row):
    budget = json.loads((row / "budget.json").read_text())
    result = hook.result(row)
    why = stage.audit(entry["sid"], row, BIGODAFNY / entry["path"])
    agent_said = result.get("outcome", "no result")
    return {"sid": entry["sid"], "arm": arm, "batch": batch, "stratum": entry["stratum"], "truth": entry["truth"],
            "path": entry["path"],
            **{k: result.get(k) for k in KEPT},
            "outcome": "proved" if agent_said == "proved" and not why else "unresolved",
            "agent_outcome": agent_said, "audit_failures": why,
            "attempts": budget["attempts"], "fuzz_calls": budget.get("fuzz_calls", 0),
            "stop_error": budget.get("stop_error"),
            "seconds": round(budget["ended"] - budget["started"]) if "ended" in budget else None}


def main():
    parser = argparse.ArgumentParser(prog="collect.py")
    parser.add_argument("--arm", required=True, choices=ARM_NAMES)
    parser.add_argument("--batch", required=True)
    args = parser.parse_args()
    root, out = STAGE / args.arm, ARMS / "runs" / args.arm / args.batch
    if out.exists() and args.batch != TRIAL:
        raise SystemExit(f"{out} exists")
    shutil.rmtree(out, ignore_errors=True)                         # only a trial reaches here with `out`
    records = []
    for entry in read_jsonl(ARMS / "manifest.jsonl"):
        if str(entry["batch"]) == args.batch:
            records.append(record(args.arm, args.batch, entry, root / entry["sid"]))
            r, results = records[-1], hook.pg.read_budget(root / entry["sid"]).get("results", {})
            print(r["sid"], r["outcome"], f"agent said {r['agent_outcome']}",
                  f"results {len(results)}/{r['attempts']}", r["audit_failures"] or "")
    shutil.copytree(root, out, ignore=shutil.ignore_patterns(".locks"))
    (out / "traj.jsonl").write_text("".join(json.dumps(r, sort_keys=True) + "\n" for r in records))
    shutil.rmtree(root)
    print(f"-> {out}")


if __name__ == "__main__":
    main()
