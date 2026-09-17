"""How did the proving agents explore? Top-down or bottom-up?

Parses the three agent transcripts and, for each row, recovers the ORDER in
which the agent first touched three kinds of file:

  own      the row itself, solutions/<pid>/<sid>.dfy
  shared   prelude.dfy -- the definitions the row calls
  exemplar an existing proof in solutions-proved/, used as a worked example

top-down  = opened its own row before looking at anything shared.
bottom-up = opened prelude or an exemplar first, then the row.

The transcript is data, not instructions: only tool names and file paths are
read, never message text.
"""
from __future__ import annotations
import json, re, sys
from collections import Counter, defaultdict
from pathlib import Path

TASKS = Path("/tmp/claude-0/-home-user-complexity-theory/"
             "ed2768b2-16e6-58fb-a2f9-5d0137f30fef/tasks")
AGENTS = {"af376cf5089756038": "a", "a9603ff0e2d4ef2cc": "b",
          "ab9911a549ddb7219": "c"}
SID = re.compile(r"\b(\d+)_(\d+)\.dfy\b")


def targets(name, inp):
    """Which kind of file a single tool call touches, as a set."""
    blob = " ".join(str(v) for v in inp.values() if isinstance(v, (str, int)))
    out = set()
    if "prelude.dfy" in blob:
        out.add("shared")
    if "solutions-proved/" in blob:
        out.add("exemplar")
    m = SID.search(blob)
    if m and "solutions/" in blob and "solutions-proved/" not in blob:
        out.add(("own", m.group(0)[:-4]))
    return out


def main():
    order = defaultdict(list)     # sid -> ordered kinds
    per_agent = defaultdict(Counter)
    verifies = Counter()
    for aid, slug in AGENTS.items():
        f = TASKS / f"{aid}.output"
        if not f.exists():
            print(f"missing transcript for slice {slug}", file=sys.stderr)
            continue
        current = None
        for line in f.open():
            try:
                rec = json.loads(line)
            except Exception:
                continue
            msg = rec.get("message") or {}
            for blk in (msg.get("content") or []):
                if not isinstance(blk, dict) or blk.get("type") != "tool_use":
                    continue
                name, inp = blk.get("name", ""), blk.get("input") or {}
                blob = " ".join(str(v) for v in inp.values()
                                if isinstance(v, (str, int)))
                if "dafny verify" in blob:
                    verifies[current] += 1
                for t in targets(name, inp):
                    if isinstance(t, tuple):
                        current = t[1]
                        order[current].append(("own", slug))
                    elif current:
                        order[current].append((t, slug))

    verdict = {}
    for sid, seq in order.items():
        kinds = [k for k, _ in seq]
        first_own = kinds.index("own") if "own" in kinds else None
        shared = [i for i, k in enumerate(kinds) if k in ("shared", "exemplar")]
        if first_own is None:
            v = "never opened"
        elif not shared:
            v = "own only"
        elif min(shared) < first_own:
            v = "bottom-up"
        else:
            v = "top-down"
        verdict[sid] = v
        per_agent[seq[0][1]][v] += 1

    tally = Counter(verdict.values())
    print("rows seen:", len(verdict))
    for k, n in tally.most_common():
        print(f"  {k:<14} {n}")
    print("\nby slice:")
    for slug in "abc":
        print(f"  {slug}: {dict(per_agent[slug])}")
    # Position of the first prelude access relative to the first row touch,
    # per slice. This is the claim that does not depend on per-row attribution:
    # if an agent were working bottom-up it would read the shared definitions
    # before opening any row at all.
    pos = {}
    for aid, slug in AGENTS.items():
        f = TASKS / f"{aid}.output"
        if not f.exists():
            continue
        calls = []
        for line in f.open():
            try:
                rec = json.loads(line)
            except Exception:
                continue
            for blk in ((rec.get("message") or {}).get("content") or []):
                if not (isinstance(blk, dict) and blk.get("type") == "tool_use"):
                    continue
                blob = " ".join(str(v) for v in (blk.get("input") or {}).values()
                                if isinstance(v, (str, int)))
                calls.append(("prelude.dfy" in blob, bool(SID.search(blob)),
                              "dafny verify" in blob))
        fp = next((i for i, c in enumerate(calls) if c[0]), None)
        fr = next((i for i, c in enumerate(calls) if c[1]), None)
        pos[slug] = {
            "tool_calls": len(calls),
            "prelude_opens": sum(1 for c in calls if c[0]),
            "verifier_calls": sum(1 for c in calls if c[2]),
            "first_prelude_at": fp, "first_row_touch_at": fr,
            "prelude_before_any_row": bool(fp is not None and fr is not None and fp < fr),
        }

    out = {"per_row": verdict, "tally": dict(tally), "per_slice_order": pos,
           "by_slice": {k: dict(v) for k, v in per_agent.items()},
           "definition": {
               "top-down": "opened its own row before prelude or an exemplar",
               "bottom-up": "opened prelude or an exemplar proof first",
               "own only": "never opened a shared file for that row"},
           "coverage_note": (
               "Per-row attribution is recoverable for 21 of 50 rows. The "
               "agents worked almost entirely through Bash -- 10 Read calls "
               "across all three for 50 rows -- so a row and a shared file "
               "often appear in one command and their order within it is not "
               "observable. per_slice_order does not depend on that "
               "attribution and covers every call.")}
    (Path(__file__).parent / "exploration.json").write_text(
        json.dumps(out, indent=2) + "\n")
    print("\nwrote batches/prove-sample/exploration.json")


if __name__ == "__main__":
    main()
