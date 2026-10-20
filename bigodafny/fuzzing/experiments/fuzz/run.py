"""Run a row's step counter on inputs from a generator; print one table.

The generator is a Python file the agent writes. It defines

    GRID = [{"n": 8}, {"n": 16}, ...]      # input sizes, one dict per row of the table
    FAMILIES = {"random": f, ...}          # f(rng, **sizes) -> input text (stdin form)

Every family runs `--per` times at each grid point. An input that breaks the
problem's stated limits or Solve's `requires` is not run. For each grid
point the table shows the costliest input: its steps, the value of the bound
(`TraceBoundValue`) and steps / bound, and the iterations of the loops that
run most. Loop counts come from rerunning only that input with the loop heads
traced, so the batch itself runs untraced. The row's stored tests run too.

    python3 experiments/fuzz/run.py SID --dfy row.dfy --gen gen.py [--per 3]

Results go to `--out` (default: `run/` beside the generator): `runs.jsonl`,
one line per input, and `worst/<k>.txt`, the input behind table row k.
"""
from __future__ import annotations
import argparse, json, random, runpy, sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))       # fuzzing/
from steptrace import Runner, build  # first: it puts bigodafny/ on sys.path
from common import _in_spec, log, write_jsonl

TOP = 5                                  # loops shown


def run_input(r, text, timeout):
    if not _in_spec(r.task, text):
        return {"status": "limits"}
    return r.run(text, timeout=timeout)


def loop_hits(r, text, timeout):
    """{point id: hits} at the loop heads, for one input."""
    res = r.run(text, timeout=timeout)
    return {int(k): v[0] for k, v in res.get("hits", {}).items()} if res["status"] == "ok" else {}


def main(argv=None):
    ap = argparse.ArgumentParser(prog="run.py")
    ap.add_argument("sid")
    ap.add_argument("--dfy", required=True, help="the row with ghost steps and, optionally, a bound")
    ap.add_argument("--gen", required=True, help="the generator: GRID and FAMILIES")
    ap.add_argument("--per", type=int, default=3, help="inputs per family and grid point")
    ap.add_argument("--timeout", type=int, default=10, help="seconds per input")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--out", help="output directory (default: run/ beside the generator)")
    a = ap.parse_args(argv)
    gen = runpy.run_path(a.gen)
    out = Path(a.out) if a.out else Path(a.gen).resolve().parent / "run"

    r = Runner(a.sid, dfy=a.dfy)
    for n in r.notes:
        log(f"{a.sid}: {n}")
    stored = [run_input(r, t, a.timeout) for t in r.seeds()]

    recs, worst = [], []
    for g, sizes in enumerate(gen["GRID"]):
        best = None
        for fam, f in gen["FAMILIES"].items():
            for k in range(a.per):
                rng = random.Random(f"{a.seed}/{g}/{fam}/{k}")
                try:
                    text = f(rng, **sizes)
                except Exception as e:
                    res = {"status": "gen", "error": f"{type(e).__name__}: {e}"[:300]}
                else:
                    res = run_input(r, text, a.timeout)
                rec = {"grid": g, "sizes": sizes, "family": fam, "k": k, **res}
                rec.pop("hits", None)
                recs.append(rec)
                if res["status"] == "ok" and (best is None or res["steps"] > best[0]["steps"]):
                    best = (rec, text)
        worst.append(best)
    r.close()

    # Rerun each grid point's costliest input with only the loop heads traced.
    _, points, _, _ = build(a.sid, "", a.dfy)
    loops = [p for p in points if p["Kind"] == "loop"]
    hits, src = [{} for _ in worst], {}
    if loops and any(worst):
        rt = Runner(a.sid, trace=",".join(sorted({str(p["Line"]) for p in loops})), dfy=a.dfy)
        traced = [p for p in rt.points if p["Kind"] == "loop"]
        src = {p["Line"]: f"{p['Method']}: {p['src']}" for p in traced}
        for k, w in enumerate(worst):
            if w:
                h = loop_hits(rt, w[1], a.timeout * 10)
                hits[k] = {p["Line"]: h.get(p["Id"], 0) for p in traced}
        rt.close()
    last = next((h for h in reversed(hits) if h), {})
    shown = sorted(last, key=lambda line: -last[line])[:TOP]

    write_jsonl(out / "runs.jsonl", recs)
    (out / "worst").mkdir(parents=True, exist_ok=True)
    for k, w in enumerate(worst):
        if w:
            (out / "worst" / f"{k}.txt").write_text(w[1], encoding="utf-8")

    head = f"{'k':>2}  {'sizes':<18} {'family':<10} {'steps':>10} {'bound':>12} {'ratio':>6}"
    print(head + "".join(f" {'L' + str(line):>9}" for line in shown))
    for k, w in enumerate(worst):
        sizes = " ".join(f"{n}={v}" for n, v in gen["GRID"][k].items())
        if not w:
            print(f"{k:>2}  {sizes:<18} {'-':<10} {'no ok run':>10}")
            continue
        rec = w[0]
        bound = rec.get("bound")
        ratio = f"{rec['steps'] / bound:.3f}" if bound else "-"
        print(f"{k:>2}  {sizes:<18} {rec['family']:<10} {rec['steps']:>10} "
              f"{bound if bound is not None else '-':>12} {ratio:>6}"
              + "".join(f" {hits[k].get(line, '-'):>9}" for line in shown))
    for line in shown:
        print(f"  L{line:<4} {src[line]}")
    if len(last) > TOP:
        print(f"  ({len(last) - TOP} more loops not shown)")

    st = Counter(x["status"] for x in recs)
    print("generated:", dict(st))
    ok = [x for x in stored if x["status"] == "ok"]
    ratios = [x["steps"] / x["bound"] for x in ok if x.get("bound")]
    print(f"stored tests: {dict(Counter(x['status'] for x in stored))}; "
          f"bound broken on {sum(x.get('bound_ok') is False for x in ok)}"
          + (f"; max steps/bound {max(ratios):.3f}" if ratios else ""))
    broken = sum(x.get("bound_ok") is False for x in recs)
    if broken:
        print(f"BOUND BROKEN on {broken} generated inputs")
    log(f"-> {out}/")
    return 0


if __name__ == "__main__":
    sys.exit(main())
