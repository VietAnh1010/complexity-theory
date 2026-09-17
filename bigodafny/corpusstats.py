"""Structural profile of the whole screened corpus, not a sample.

Every figure is computed from the files in solutions/ on this run. Dafny size
is measured on the METHOD BODY with comments stripped, because each row's
header carries the original Python verbatim and counting that would report the
Python's size as the Dafny's.
"""
from __future__ import annotations
import json, re, statistics, sys
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE / "experiments"))
from common import DATA, SOLUTIONS, write_json           # noqa: E402
from features import extract, split_file, strip_comments  # noqa: E402

PY_LINE = re.compile(r"^// ?(.*)$")


def python_loc(header):
    """Lines of the original Python, which each header quotes verbatim.

    The block opens with `// --- Python ---...` and closes with a plain rule
    line, so the opener has to be matched on its own -- a single `-{20,}`
    pattern misses it and silently returns zero for every row.
    """
    inside, n = False, 0
    for line in header.splitlines():
        if not inside and re.match(r"^//\s*-+\s*Python\s*-+", line):
            inside = True
            continue
        if inside:
            if re.match(r"^//\s*-{20,}\s*$", line):
                break
            m = PY_LINE.match(line)
            if m and m.group(1).strip():
                n += 1
    return n


def loc(code):
    return sum(1 for l in code.splitlines() if l.strip())


def pct(xs, p):
    xs = sorted(xs)
    return xs[min(len(xs) - 1, int(round(p / 100 * (len(xs) - 1))))]


def main():
    ds = {r["solution_id"]: r for r in
          (json.loads(l) for l in (DATA / "dataset.jsonl").open())}
    depth = {r["sid"]: r for r in
             (json.loads(l) for l in (DATA / "call_depth.jsonl").open())}

    rows = []
    for f in sorted(SOLUTIONS.rglob("*.dfy")):
        text = f.read_text(encoding="utf-8")
        header, body_raw = split_file(text)
        body = strip_comments(body_raw)
        ft = extract(text)
        sid = f.stem
        d = depth.get(sid, {})
        rows.append({
            "solution_id": sid,
            "label": (ds.get(sid) or {}).get("time_complexity_inferred"),
            "dafny_loc": loc(body),
            "python_loc": python_loc(header),
            "loops": ft["loops"],
            "loop_depth": ft["loop_depth"],
            "data_dependent_loops": ft["data_dependent_loops"],
            "recursive_helpers": ft["recursive_helpers"],
            "seq_args": ft["seq_args"],
            "call_depth": d.get("longest_chain"),
            "reachable": d.get("reachable"),
            "own_decls": d.get("own_decls"),
            "prelude_calls": d.get("prelude_calls") or [],
        })

    dl = [r["dafny_loc"] for r in rows]
    pl = [r["python_loc"] for r in rows if r["python_loc"]]
    ratio = [r["dafny_loc"] / r["python_loc"]
             for r in rows if r["python_loc"] and r["dafny_loc"]]

    def dist(key):
        return dict(sorted(Counter(r[key] for r in rows).items(),
                           key=lambda kv: (kv[0] is None, kv[0])))

    out = {
        "scope": "solutions/", "rows": len(rows),
        "dafny_loc": {
            "total": sum(dl), "mean": round(statistics.mean(dl), 1),
            "median": statistics.median(dl), "min": min(dl), "max": max(dl),
            "p90": pct(dl, 90), "p99": pct(dl, 99),
        },
        "python_loc": {
            "total": sum(pl), "mean": round(statistics.mean(pl), 1),
            "median": statistics.median(pl), "min": min(pl), "max": max(pl),
        },
        "expansion": {
            "median_dafny_over_python": round(statistics.median(ratio), 2),
            "mean": round(statistics.mean(ratio), 2),
            "rows_smaller_in_dafny": sum(1 for x in ratio if x < 1),
        },
        "loops": {
            "distribution": dist("loops"),
            "loopless_rows": sum(1 for r in rows if r["loops"] == 0),
            "max": max(r["loops"] for r in rows),
        },
        "loop_depth": {
            "distribution": dist("loop_depth"),
            "nested": sum(1 for r in rows if r["loop_depth"] >= 2),
        },
        "data_dependent_loops": {
            "distribution": dist("data_dependent_loops"),
            "rows_with_any": sum(1 for r in rows if r["data_dependent_loops"]),
        },
        "call_depth": {
            "distribution": dist("call_depth"),
            "median": statistics.median(r["call_depth"] for r in rows),
            "mean": round(statistics.mean(r["call_depth"] for r in rows), 2),
        },
        "recursive_helpers": {
            "rows_with_own_recursion": sum(1 for r in rows if r["recursive_helpers"]),
        },
        "own_decls": dist("own_decls"),
        "prelude": {
            "frequency": dict(Counter(
                fn for r in rows for fn in r["prelude_calls"]).most_common()),
            "rows_using_none": sum(1 for r in rows if not r["prelude_calls"]),
            "median_per_row": statistics.median(
                len(r["prelude_calls"]) for r in rows),
        },
        "labels": dict(Counter(r["label"] for r in rows).most_common()),
        "rows_detail": rows,
    }
    write_json(DATA / "corpus_stats.json", out)
    print(f"solutions/: {out['rows']} rows")
    print(f"  Dafny LoC   total {out['dafny_loc']['total']}  "
          f"median {out['dafny_loc']['median']}  max {out['dafny_loc']['max']}")
    print(f"  Python LoC  total {out['python_loc']['total']}  "
          f"median {out['python_loc']['median']}")
    print(f"  expansion   median {out['expansion']['median_dafny_over_python']}x")
    print(f"  loop depth  {out['loop_depth']['distribution']}")
    print(f"  call depth  {out['call_depth']['distribution']}")


if __name__ == "__main__":
    main()
