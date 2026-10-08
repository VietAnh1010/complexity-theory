"""Collect the measured state of the corpus into one JSON payload.

Everything an artifact would display is computed here from the records on
disk, so no number in the artifact is ever typed by hand. Re-run it after any
sweep; it writes only out/artifact_data.json (git-ignored).
"""
from __future__ import annotations
import json, re, statistics, subprocess
from collections import Counter
from pathlib import Path

from common import PROVED, OUT, SOLUTIONS, z3_version
import prove_stats
from features import extract, split_file, strip_comments

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


def callgraph(depth):
    """Structure of solutions/ as walked by callgraph.py.

    Descriptive only -- no outcome join lives here. The record covers
    solutions/ and nothing else, and it was current when this was written:
    354 rows, no dead paths, no truncated search.
    """
    if not depth:
        return {"status": "no record"}
    rows = list(depth.values())
    prelude = Counter(f for r in rows for f in (r.get("prelude_calls") or []))
    # A proof adds ghost helpers, which can lengthen the longest chain. The
    # gap says how much instrumentation the corpus's proofs actually add.
    deepened = [r for r in rows
                if (r.get("longest_chain_with_ghost") or 0) > (r.get("longest_chain") or 0)]
    return {
        "scope": "solutions/", "rows": len(rows),
        "depth_distribution": dict(sorted(Counter(
            r["longest_chain"] for r in rows).items())),
        "median_depth": sorted(r["longest_chain"] for r in rows)[len(rows) // 2],
        "recursive": sum(1 for r in rows if r.get("recursive")),
        "self_contained_depth_0_1": sum(1 for r in rows if r["longest_chain"] <= 1),
        "reachable_distribution": dict(sorted(Counter(
            r.get("reachable", 0) for r in rows).items())),
        "own_decls_distribution": dict(sorted(Counter(
            r.get("own_decls", 0) for r in rows).items())),
        "rows_deepened_by_ghost": len(deepened),
        "prelude_calls_total": sum(prelude.values()),
        "prelude_call_frequency": dict(prelude.most_common()),
        "rows_using_no_prelude": sum(1 for r in rows if not r.get("prelude_calls")),
        "search_truncated": sum(1 for r in rows if r.get("search_truncated")),
    }


def proofs_all(depth, ds, pv_rows):
    """Every proof file, tagged `campaign` when a campaign's bounded agent proved
    the row and `other` otherwise (proved before the campaigns or by hand)."""
    files = sorted(PROVED.rglob("*.dfy"))
    campaign = {r["solution_id"] for r in pv_rows if r["outcome"] == "proved"}
    rows = []
    for f in files:
        sid = f.stem
        d, rec = depth.get(sid, {}), ds.get(sid, {})
        m = re.search(r"ensures\s+steps\s*<=\s*(.+)", f.read_text(encoding="utf-8"))
        rows.append({
            "solution_id": sid,
            "file": str(f.relative_to(HERE)),
            "era": "campaign" if sid in campaign else "other",
            "label": rec.get("time_complexity_inferred"),
            "bound": (m.group(1).split("//")[0].strip() if m else None),
            "call_depth": d.get("longest_chain"),
            "recursive": d.get("recursive"),
        })
    sids = {r["solution_id"] for r in rows}
    return {
        "files": len(rows), "rows": len(sids),
        "by_era": dict(Counter(r["era"] for r in rows)),
        "rows_with_two_proofs": sorted(
            sid for sid in sids
            if sum(1 for r in rows if r["solution_id"] == sid) > 1),
        "by_label": dict(Counter(r["label"] for r in rows).most_common()),
        "entries": rows,
    }


def difficulty(pv_rows):
    """Does structure predict whether a proof closes?

    Joins both campaigns' outcomes against call depth and recursion. The
    label is already known to matter -- linear rows close far more often than
    `O(nlogn)` ones -- so this asks whether depth adds anything beyond it.
    """
    done = [r for r in pv_rows if r["outcome"] in ("proved", "unresolved")]
    if not done:
        return {"status": "not yet run"}

    def rate(key):
        out = {}
        for r in done:
            k = r.get(key)
            k = "unknown" if k is None else str(k)
            a, b = out.setdefault(k, [0, 0])
            out[k] = [a + (r["outcome"] == "proved"), b + 1]
        return {k: {"proved": v[0], "of": v[1]} for k, v in sorted(out.items())}

    return {
        "n": len(done),
        "by_call_depth": rate("call_depth"),
        "by_recursive": rate("recursive"),
        "by_label": rate("label"),
        "note": ("Label dominates. Depth is reported so the claim can be "
                 "checked rather than asserted; with the sample split "
                 "across several depths, treat any depth effect as "
                 "indicative."),
    }


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


def corpus_stats(ds, depth):
    """Structural profile of solutions/: Dafny body size with comments
    stripped (each header quotes the Python verbatim), loops, call depth."""
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
    return out


def main():
    ds = {r["solution_id"]: r for r in jsonl(DATA / "dataset.jsonl")}
    ver = {r["solution_id"]: r for r in jsonl(DATA / "verification.jsonl")}
    depth = {r["sid"]: r for r in jsonl(DATA / "call_depth.jsonl")}
    stats = json.loads((DATA / "stats.json").read_text())
    campaigns = prove_stats.payload()
    # the bounded agents' draws, joined to call depth for the difficulty table
    draws = [dict(r, call_depth=depth.get(r["solution_id"], {}).get("longest_chain"),
                  recursive=depth.get(r["solution_id"], {}).get("recursive"))
             for r in campaigns["rows"] if not r["redrawn"]]

    dirs = {d.name: sum(1 for _ in d.rglob("*.dfy"))
            for d in sorted(HERE.glob("solutions*")) if d.is_dir()}

    optout = sorted(s for s, r in ver.items() if r.get("termination_opt_out"))
    # A row that verifies with `decreases *` has every obligation discharged
    # EXCEPT termination, which it opted out of. Counting it as verified
    # without saying so overstates the guarantee.
    fully = [s for s, r in ver.items()
             if r["verified"] and not r.get("termination_opt_out")]

    payload = {
        "generated": git("log", "-1", "--format=%cI", default=""),
        "commit": git("rev-parse", "--short", "HEAD"),
        "branch": git("rev-parse", "--abbrev-ref", "HEAD"),
        "toolchain": {"dafny": stats.get("dafny_version"), "z3": z3_version()},

        "corpus": {
            "rows": stats["rows"], "problems": stats["problems"],
            "directories": dirs,
            "splits": stats["splits"],
            "dafny_status": stats["dafny_status"],
            "time_complexity": stats["time_complexity"],
        },

        "verification": {
            # The sweep covers solutions-ungateable/ as well, since those rows
            # are translated and their safety record would otherwise vanish
            # when they left solutions/. Reported apart, because a safety
            # result and a behaviour result are different claims.
            "scope": "solutions/ and solutions-ungateable/",
            "total": len(ver),
            "verified": sum(r["verified"] for r in ver.values()),
            "fully_verified_incl_termination": len(fully),
            "termination_opt_out": optout,
            "by_directory": dict(Counter(
                r["path"].split("/")[0] for r in ver.values())),
            "failing": sorted(s for s, r in ver.items() if not r["verified"]),
            "failure_kinds": dict(Counter(
                r["kind"] for r in ver.values() if not r["verified"])),
        },

        "campaigns": campaigns,
        "proofs_all": proofs_all(depth, ds, draws),
        "difficulty": difficulty(draws),

        "callgraph": callgraph(depth),
        "corpus_stats": corpus_stats(ds, depth),
    }

    out = OUT / "artifact_data.json"
    OUT.mkdir(exist_ok=True)
    out.write_text(json.dumps(payload, indent=2) + "\n")
    v = payload["verification"]
    print(f"wrote {out.relative_to(HERE)}")
    print(f"  verification: {v['verified']}/{v['total']} verified, "
          f"{v['fully_verified_incl_termination']} incl. termination")
    print(f"  campaigns: {campaigns['proved']}/{campaigns['drawn']} proved")


if __name__ == "__main__":
    main()
