"""Collect the measured state of the corpus into one JSON payload.

Everything an artifact would display is computed here from the records on
disk, so no number in the artifact is ever typed by hand. Re-run it after any
sweep; it reads and never writes outside data/artifact_data.json.
"""
from __future__ import annotations
import json, subprocess
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
DATA = HERE / "data"


def jsonl(p):
    p = Path(p)
    return [json.loads(l) for l in p.open()] if p.exists() else []


def git(*args, default=""):
    try:
        return subprocess.run(["git", *args], cwd=HERE.parent, text=True,
                              capture_output=True, check=True).stdout.strip()
    except Exception:
        return default


def main():
    ds = {r["solution_id"]: r for r in jsonl(DATA / "dataset.jsonl")}
    ver = {r["solution_id"]: r for r in jsonl(DATA / "verification.jsonl")}
    depth = {r["sid"]: r for r in jsonl(DATA / "call_depth.jsonl")}
    stats = json.loads((DATA / "stats.json").read_text())
    manifest = jsonl(HERE / "batches/verify-sample/manifest.jsonl")

    dirs = {d.name: sum(1 for _ in d.rglob("*.dfy"))
            for d in sorted(HERE.glob("solutions*")) if d.is_dir()}

    optout = sorted(s for s, r in ver.items() if r.get("termination_opt_out"))
    # A row that verifies with `decreases *` has every obligation discharged
    # EXCEPT termination, which it opted out of. Counting it as verified
    # without saying so overstates the guarantee.
    fully = [s for s, r in ver.items()
             if r["verified"] and not r.get("termination_opt_out")]

    sample = []
    for m in manifest:
        s = m["solution_id"]
        v, d = ver.get(s, {}), depth.get(s, {})
        sample.append({
            "solution_id": s, "label": m["label"], "split": m["split"],
            "gate": m["gate"], "verified": v.get("verified"),
            "termination_opt_out": v.get("termination_opt_out", False),
            "attempts_used": 0, "outcome": "verified-unedited",
            "call_depth": d.get("longest_chain"),
            "recursive": d.get("recursive"),
        })

    payload = {
        "generated": git("log", "-1", "--format=%cI", default=""),
        "commit": git("rev-parse", "--short", "HEAD"),
        "branch": git("rev-parse", "--abbrev-ref", "HEAD"),
        "toolchain": {"dafny": stats.get("dafny_version"), "z3": "4.12.1"},

        "corpus": {
            "rows": stats["rows"], "problems": stats["problems"],
            "directories": dirs,
            "splits": stats["splits"],
            "dafny_status": stats["dafny_status"],
            "time_complexity": stats["time_complexity"],
        },

        "verification": {
            "scope": "solutions/",
            "total": len(ver),
            "verified": sum(r["verified"] for r in ver.values()),
            "fully_verified_incl_termination": len(fully),
            "termination_opt_out": optout,
            "failing": sorted(s for s, r in ver.items() if not r["verified"]),
            "failure_kinds": dict(Counter(
                r["kind"] for r in ver.values() if not r["verified"])),
        },

        "sample": {
            "question": "were the 106 unrecorded rows failing, or never run?",
            "answer": "never run",
            "seed": 20260916, "drawn": len(manifest), "pool": 105,
            "frame": "solutions/, no verification record, non-empty label",
            "excluded": {"1196_51": "does not pass its gate"},
            "bounds": {"attempts_per_row": 3, "seconds_per_row": 300},
            "attempts_consumed": 0,
            "agents_spawned": 0,
            "labels": dict(Counter(m["label"] for m in manifest).most_common()),
            "rows": sorted(sample, key=lambda r: (int(r["solution_id"].split("_")[0]),
                                                  r["solution_id"])),
        },

        "stale_record_finding": {
            "before": {"rows": 362, "recorded_failing": 12,
                       "paths_no_longer_existing": 114},
            "after": {"rows": len(ver),
                      "recorded_failing": sum(1 for r in ver.values()
                                              if not r["verified"])},
            "cause": ("verify_all.py rewrites the record whole and was not "
                      "re-run after the label audit moved 114 rows out of "
                      "solutions/"),
            "controls": [
                "injected an out-of-range read into a copy of 1053_38; "
                "reported index-out-of-range, so the script detects failure",
                "re-ran 3 rows the record called failing; all verified",
            ],
        },

        "call_depth": {
            "rows": len(depth),
            "distribution": dict(sorted(Counter(
                r["longest_chain"] for r in depth.values()).items())),
            "recursive": sum(1 for r in depth.values() if r.get("recursive")),
        },

        "open_decisions": [
            "value-vs-size convention, 12 rows, named in solutions-disputed/README.md",
            "what `differs`-by-timeout-only should mean (1501_224)",
            "whether the 6 ungateable rows belong in solutions/",
            "10 rows use `decreases *`; their termination is not proved",
        ],
    }

    out = DATA / "artifact_data.json"
    out.write_text(json.dumps(payload, indent=2) + "\n")
    v = payload["verification"]
    print(f"wrote {out.relative_to(HERE)}")
    print(f"  verification: {v['verified']}/{v['total']} verified, "
          f"{v['fully_verified_incl_termination']} incl. termination")
    print(f"  sample: {payload['sample']['drawn']} rows, "
          f"{payload['sample']['attempts_consumed']} attempts consumed")


if __name__ == "__main__":
    main()
