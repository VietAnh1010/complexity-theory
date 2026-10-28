"""The `blind-guess` agent's `fuzz` command, the only command `guard.py` lets its Bash run.

    .venv/bin/python3 experiments/fuzz/fuzz.py DFY GEN [--per N] [--bound E] [--counter NAME] [--time-limit S]

Runs the row's step counter on inputs from the agent's GEN and prints one table.
The row's SID is the name of DFY's directory. GEN defines

    GRID = [{"n": 8}, {"n": 16}, ...]      # input sizes, one dict per table row
    FAMILIES = {"random": f, ...}          # f(rng, **sizes) -> input text, as on stdin

Each family runs N times at each grid point. GEN runs in a child process, so
nothing it prints reaches the table. An input is skipped as `out-of-spec` when it
breaks Solve's `requires` or a limit in `data/constraints.jsonl`.

For each grid point the table shows the costliest input: its steps, the bound
and steps / bound, and how often the busiest loops ran. Loop counts come from
rerunning that one input with only the loop heads traced.

`--bound E` runs a copy of DFY with `ensures steps <= E` added to Solve. The copy
lies beside DFY while it runs. `--counter NAME` names the counter when it is not
`steps`; `guard.py` does not accept it.

`--time-limit S` (default `TIME_LIMIT`): inputs and loop reruns not started within S
seconds are skipped, so a call ends within S plus one input and one rerun.
`guard.py` does not accept it, so agents get the default.

Call k writes `attempts/<k>/table.txt` beside DFY: the DFY name, E, the attempt
holding the GEN that ran, then the output. It copies GEN to `attempts/<k>/gen.py`
only when GEN changed since the last copy.
"""
from __future__ import annotations
import argparse, json, random, re, runpy, subprocess, sys, time
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))       # fuzzing/
from steptrace import Runner, build  # first: it puts bigodafny/ on sys.path
from common import _in_spec

TOP = 5                                  # loops shown
TIMEOUT = 10                             # seconds per input
TIME_LIMIT = 300                         # seconds per call; under the Bash tool's 600


def generate(gen, per):
    """GRID, and every input GEN makes as [point, family, text or None, error or None]."""
    module = runpy.run_path(gen)
    inputs = []
    for point, sizes in enumerate(module["GRID"]):
        for family, make in module["FAMILIES"].items():
            for copy in range(per):
                try:
                    text = make(random.Random(f"{point}/{family}/{copy}"), **sizes)
                    inputs.append([point, family, text, None])
                except Exception as e:
                    inputs.append([point, family, None, f"{family} at {sizes}: {type(e).__name__}: {e}"[:300]])
    return module["GRID"], inputs


def run_generator(gen, per, timeout):
    """`generate` in a child process: GRID and the inputs."""
    child = subprocess.run([sys.executable, __file__, "--gen", gen, str(per)],
                           capture_output=True, text=True, timeout=timeout)
    if child.returncode:
        raise RuntimeError(f"gen.py failed:\n{child.stderr.strip()[-1000:]}")
    return json.loads(child.stdout.splitlines()[-1])           # GEN's own prints come first


def run_inputs(runner, inputs, points, deadline):
    """Run every input. Returns the status counts, the bound breaks, the first
    generator and parse errors, and per point the costliest (family, result, text)."""
    statuses, broken, gen_error, parse_error = Counter(), 0, None, None
    costliest = [None] * points
    newline = any(seed.endswith("\n") for seed in runner.seeds())    # as the row's stored tests end
    for point, family, text, error in inputs:
        if text is not None:
            text = text.removesuffix("\n")
            if newline:
                text += "\n"
        if error:
            result = {"status": "gen"}
            gen_error = gen_error or error
        elif not _in_spec(runner.task, text):
            result = {"status": "out-of-spec"}
        elif time.monotonic() > deadline:
            result = {"status": "time-limit"}
        else:
            result = runner.run(text, timeout=TIMEOUT)
        statuses[result["status"]] += 1
        if result["status"] == "parse":
            parse_error = parse_error or f"{family}: {result['error']}"
        broken += result.get("bound_ok") is False
        if result["status"] == "ok" and (costliest[point] is None
                                         or result["steps"] > costliest[point][1]["steps"]):
            costliest[point] = (family, result, text)
    return statuses, broken, gen_error, parse_error, costliest


def loop_counts(sid, dfy, costliest, counter, deadline):
    """Rerun each point's costliest input with the loop heads traced.
    Returns per point {line: iterations}, and {line: loop source}."""
    _, points, _, _ = build(sid, "", dfy, counter)
    lines = sorted({str(p["Line"]) for p in points if p["Kind"] == "loop"})
    counts = [{} for _ in costliest]
    if not lines or not any(costliest):
        return counts, {}
    runner = Runner(sid, trace=",".join(lines), dfy=dfy, counter=counter)
    loops = [p for p in runner.points if p["Kind"] == "loop"]
    source = {p["Line"]: f"{p['Method']}: {p['src']}" for p in loops}
    for point, worst in enumerate(costliest):
        if worst and time.monotonic() < deadline:
            result = runner.run(worst[2], timeout=TIMEOUT * 10)
            hits = {int(i): v[0] for i, v in result.get("hits", {}).items()} if result["status"] == "ok" else {}
            counts[point] = {p["Line"]: hits.get(p["Id"], 0) for p in loops}
    runner.close()
    return counts, source


def format_table(grid, costliest, counts, source):
    """The table's lines: one per grid point, then the shown loops' source."""
    last = next((c for c in reversed(counts) if c), {})
    shown = sorted(last, key=lambda line: -last[line])[:TOP]
    lines = [f"{'k':>2}  {'sizes':<18} {'family':<10} {'steps':>10} {'bound':>12} {'ratio':>6}"
             + "".join(f" {'L' + str(line):>9}" for line in shown)]
    for point, worst in enumerate(costliest):
        sizes = " ".join(f"{name}={value}" for name, value in grid[point].items())
        if not worst:
            lines.append(f"{point:>2}  {sizes:<18} {'-':<10} {'no ok run':>10}")
            continue
        family, result, _ = worst
        bound = result.get("bound")
        ratio = f"{result['steps'] / bound:.3f}" if bound else "-"
        lines.append(f"{point:>2}  {sizes:<18} {family:<10} {result['steps']:>10} "
                     f"{bound if bound is not None else '-':>12} {ratio:>6}"
                     + "".join(f" {counts[point].get(line, '-'):>9}" for line in shown))
    lines += [f"  L{line:<4} {source[line]}" for line in shown]
    if len(last) > TOP:
        lines.append(f"  ({len(last) - TOP} more loops not shown)")
    return lines


def fuzz(dfy, gen, per=3, counter="steps", time_limit=TIME_LIMIT):
    """Run GEN's inputs on DFY and return the table as text."""
    deadline = time.monotonic() + time_limit
    sid = Path(dfy).parent.name
    grid, inputs = run_generator(gen, per, time_limit)
    runner = Runner(sid, dfy=dfy, counter=counter)
    notes = [f"note: {n}" for n in runner.notes]
    statuses, broken, gen_error, parse_error, costliest = run_inputs(runner, inputs, len(grid), deadline)
    runner.close()
    counts, source = loop_counts(sid, dfy, costliest, counter, deadline)
    lines = notes + format_table(grid, costliest, counts, source)
    lines.append(f"generated: {dict(statuses)}")
    if time.monotonic() > deadline:
        lines.append(f"TIME LIMIT {time_limit} s reached: later inputs and loop reruns were skipped")
    if gen_error:
        lines.append(f"first generator error: {gen_error}")
    if parse_error:
        lines.append(f"first parse error: {parse_error}")
    if broken:
        lines.append(f"BOUND BROKEN on {broken} generated inputs")
    return "\n".join(lines)


def add_bound(text, bound, counter="steps"):
    """TEXT with `ensures COUNTER <= BOUND` added to Solve's signature."""
    if not (m := re.search(rf"method Solve\b.*?ghost {counter}: nat\)", text, re.S)):
        raise ValueError(f"no `method Solve ... ghost {counter}: nat)` to add the bound to")
    return text[:m.end()] + f"\n  ensures {counter} <= {bound}" + text[m.end():]


def keep_gen(row_dir, attempt, gen_text):
    """The attempt number whose gen.py equals GEN_TEXT: the latest copy, else a new
    copy in ATTEMPT."""
    copies = [int(p.parent.name) for p in row_dir.glob("attempts/*/gen.py")]
    if copies and (row_dir / "attempts" / str(max(copies)) / "gen.py").read_text() == gen_text:
        return max(copies)
    (row_dir / "attempts" / str(attempt) / "gen.py").write_text(gen_text)
    return attempt


def main():
    parser = argparse.ArgumentParser(prog="fuzz.py")
    parser.add_argument("dfy", help="absolute path of the .dfy file")
    parser.add_argument("gen", help="absolute path of gen.py")
    parser.add_argument("--per", type=int, default=3, help="inputs per family and grid point")
    parser.add_argument("--bound", help="E: run DFY with `ensures steps <= E` added to Solve")
    parser.add_argument("--counter", default="steps", help="the counter's name in DFY")
    parser.add_argument("--time-limit", type=int, default=TIME_LIMIT, help="seconds for the whole call")
    args = parser.parse_args()
    dfy = Path(args.dfy)
    row_dir = dfy.parent
    attempt = len(list(row_dir.glob("attempts/*"))) + 1
    attempt_dir = row_dir / "attempts" / str(attempt)
    attempt_dir.mkdir(parents=True)
    header = [f"dfy: {dfy.name}"] + ([f"bound: {args.bound}"] if args.bound else [])
    run_dfy = row_dir / f".bound-{attempt}.dfy" if args.bound else dfy
    try:
        if args.bound:
            run_dfy.write_text(add_bound(dfy.read_text(), args.bound, args.counter))
        header.append(f"gen: attempts/{keep_gen(row_dir, attempt, Path(args.gen).read_text())}/gen.py")
        output, failed = fuzz(str(run_dfy), args.gen, args.per, args.counter, args.time_limit), False
    except Exception as e:
        output, failed = f"{type(e).__name__}: {e}", True
    finally:
        if args.bound:
            run_dfy.unlink(missing_ok=True)
    (attempt_dir / "table.txt").write_text("\n".join(header) + f"\n{output}\n")
    if failed:
        sys.exit(output)
    print(output)


if __name__ == "__main__":
    if sys.argv[1:2] == ["--gen"]:
        print(json.dumps(generate(sys.argv[2], int(sys.argv[3]))))
    else:
        main()
