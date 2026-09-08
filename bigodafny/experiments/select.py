"""Pick the 100 examples the experiment runs on.

Pool: the rows in `solutions/` -- behaviourally validated AND `dafny verify`
clean. Starting anywhere weaker would spend agents on safety obligations
instead of on complexity, which is not what this measures.

Excluded:
  * the 12 rows already in solutions-verified/ and solutions-nlogn/. Their
    finished proof is in the repo, so for the blind arm the answer leaks by
    construction.
  * siblings. One row per problem, highest score kept -- sibling rows are near
    duplicates of each other and would inflate any per-class statistic.

Deterministic: same tree in, same manifest out. No model is in this pipeline.

    python3 experiments/select.py            # write manifest.json
    python3 experiments/select.py --show     # print the class table only
"""
from __future__ import annotations
import json, sys
from collections import Counter, defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from common import DATA, SOLUTIONS, VERIFIED, NLOGN, read_jsonl   # noqa: E402
from features import extract, difficulty_static, score            # noqa: E402

HERE = Path(__file__).resolve().parent
MANIFEST = HERE / "manifest.json"
TARGET = 100


def already_proved():
    out = set()
    for d in (VERIFIED, NLOGN):
        for p in d.rglob("*.dfy"):
            out.add(p.stem)
    return out


def candidates():
    rows = {r["solution_id"]: r for r in read_jsonl(DATA / "dataset.jsonl")}
    proved = already_proved()
    rarity = Counter()
    out = []
    for p in sorted(SOLUTIONS.rglob("*.dfy")):
        sid = p.stem
        if sid in proved:
            continue
        r = rows.get(sid)
        if r is None:
            continue
        text = p.read_text(encoding="utf-8")
        if "TODO: translate" in text:
            continue
        f = extract(text)
        out.append({
            "sid": sid,
            "problem_id": r["problem_id"],
            "problem_name": r["problem_name"],
            "label": r["time_complexity_inferred"],
            "split": r["split"],
            "path": str(p.relative_to(SOLUTIONS.parent)),
            "features": f,
            "difficulty_static": difficulty_static(f),
        })
        rarity[r["time_complexity_inferred"]] += 1

    # one row per problem, the highest scoring
    for c in out:
        c["score"] = score(c["features"], 1.0 / rarity[c["label"]])
    best = {}
    for c in out:
        k = c["problem_id"]
        if k not in best or (c["score"], c["sid"]) > (best[k]["score"], best[k]["sid"]):
            best[k] = c
    return sorted(best.values(), key=lambda c: (-c["score"], c["sid"])), rarity


def stratify(pool, target=TARGET):
    """Rare classes whole, then the common ones in proportion, best score first."""
    by_class = defaultdict(list)
    for c in pool:
        by_class[c["label"]].append(c)
    for v in by_class.values():
        v.sort(key=lambda c: (-c["score"], c["sid"]))

    RARE = 6                       # a class this small is taken entire
    chosen, quota = [], {}
    rare = {k: v for k, v in by_class.items() if len(v) <= RARE}
    for k, v in rare.items():
        quota[k] = len(v)
        chosen += v

    rest = {k: v for k, v in by_class.items() if len(v) > RARE}
    left = target - len(chosen)
    total = sum(len(v) for v in rest.values())
    # largest-remainder apportionment, so the counts sum to `left` exactly
    exact = {k: left * len(v) / total for k, v in rest.items()}
    base = {k: int(x) for k, x in exact.items()}
    short = left - sum(base.values())
    for k in sorted(rest, key=lambda k: (-(exact[k] - base[k]), k))[:short]:
        base[k] += 1
    for k, n in base.items():
        n = min(n, len(rest[k]))
        quota[k] = n
        chosen += rest[k][:n]

    chosen.sort(key=lambda c: (-c["score"], c["sid"]))
    return chosen, quota


def main():
    pool, rarity = candidates()
    chosen, quota = stratify(pool)

    print(f"pool (one row per problem, unproved): {len(pool)}")
    print(f"{'class':22} {'pool':>5} {'chosen':>7}")
    for k in sorted(rarity, key=lambda k: -rarity[k]):
        inpool = sum(1 for c in pool if c["label"] == k)
        print(f"{k:22} {inpool:5} {quota.get(k, 0):7}")
    print(f"{'TOTAL':22} {len(pool):5} {len(chosen):7}")
    print()
    d = Counter(c["difficulty_static"] for c in chosen)
    print("difficulty_static:", " ".join(f"{k}:{d[k]}" for k in sorted(d)))

    if "--show" in sys.argv:
        return
    MANIFEST.write_text(json.dumps({
        "target": TARGET,
        "pool_size": len(pool),
        "quota": quota,
        "examples": chosen,
    }, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"\nwrote {MANIFEST.relative_to(Path.cwd())} ({len(chosen)} examples)")


if __name__ == "__main__":
    main()
