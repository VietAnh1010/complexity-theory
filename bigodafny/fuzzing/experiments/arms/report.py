"""Print the result tables over every collected batch but `trial` (README.md § Run)."""
from __future__ import annotations
from statistics import mean, median

from setup import ARMS, ARM_NAMES, read_jsonl

RUNS = ARMS / "runs"
STRATA = ("easy", "nlogn", "n2", "rare")
TRIAL = "trial"


def score(rec, judged):
    j = judged.get((rec["arm"], rec["sid"]), {})
    proved = rec["outcome"] == "proved"
    return {"guess": j.get("guess_ok", rec["guess"] == rec["truth"]) if rec["arm"] in ("full", "nofuzz") else None,
            "class": j.get("class_ok", rec["class"] == rec["truth"]),
            "proved": proved,
            "tight": j.get("tight") if proved else False}             # None: not judged yet


def rate(values):
    known = [v for v in values if v is not None]
    cell = f"{sum(known)}/{len(known)}" if known else "-"
    return cell + (f" ({len(values) - len(known)} unjudged)" if len(known) < len(values) else "")


def table(recs, scores):
    lines = ["| arm | rows | guess | class | proved | tight | median s | attempts | fuzz calls |",
             "|---|---:|---:|---:|---:|---:|---:|---:|---:|"]
    for arm in ARM_NAMES:
        mine = [i for i, r in enumerate(recs) if r["arm"] == arm]
        if not mine:
            continue
        secs = [recs[i]["seconds"] for i in mine if recs[i]["seconds"] is not None]
        cells = [rate([scores[i][k] for i in mine]) for k in ("guess", "class", "proved", "tight")]
        cells[0] = cells[0] if arm in ("full", "nofuzz") else "-"
        lines.append(f"| `{arm}` | {len(mine)} | " + " | ".join(cells) +
                     f" | {median(secs) if secs else '-'} | {mean(recs[i]['attempts'] for i in mine):.1f}"
                     f" | {mean(recs[i]['fuzz_calls'] for i in mine):.1f} |")
    return lines


def paired(recs, scores):
    by = {(r["arm"], r["sid"]): s for r, s in zip(recs, scores)}
    lines = ["| `full` against | metric | full only | other only |", "|---|---|---:|---:|"]
    for arm in ARM_NAMES[1:]:
        for k in ("class", "proved", "tight"):
            pairs = [(by[("full", sid)][k], s[k]) for (a, sid), s in by.items() if a == arm and ("full", sid) in by]
            pairs = [(f, o) for f, o in pairs if f is not None and o is not None]
            if pairs:
                lines.append(f"| `{arm}` | {k} | {sum(f and not o for f, o in pairs)} | {sum(o and not f for f, o in pairs)} |")
    return lines


def main():
    recs = [r for p in sorted(RUNS.glob("*/*/traj.jsonl")) if p.parent.name != TRIAL for r in read_jsonl(p)]
    judged = {(j["arm"], j["sid"]): j for p in sorted(RUNS.glob("judged-*.jsonl")) for j in read_jsonl(p)}
    scores = [score(r, judged) for r in recs]
    for name, keep in [(s, lambda r, s=s: r["stratum"] == s) for s in STRATA] + [("pooled", lambda r: True)]:
        idx = [i for i, r in enumerate(recs) if keep(r)]
        if idx:
            print(f"\n## {name}\n")
            print("\n".join(table([recs[i] for i in idx], [scores[i] for i in idx])))
    print("\n## paired, pooled\n")
    print("\n".join(paired(recs, scores)))


if __name__ == "__main__":
    main()
