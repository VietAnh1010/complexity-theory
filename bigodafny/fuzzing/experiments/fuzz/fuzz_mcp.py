"""MCP server of the `blind-guess` agent (`.claude/agents/blind-guess.md`): one tool, `fuzz`.

`fuzz(dfy, gen, per)` runs a row's step counter on inputs from the agent's
generator and returns one table. The row's SID is the name of the directory
holding `dfy`. `guard.py` checks the paths first. The generator defines

    GRID = [{"n": 8}, {"n": 16}, ...]      # input sizes, one dict per row of the table
    FAMILIES = {"random": f, ...}          # f(rng, **sizes) -> input text (stdin form)

Every family runs `per` times at each grid point. An input that breaks Solve's
`requires` is not run, nor one that breaks a limit `data/constraints.jsonl`
quotes for its problem (status `out-of-spec`); most problems have no entry
there, so their limits go unchecked. For each grid point
the table shows the costliest input: its steps, the value of the bound
(`TraceBoundValue`) and steps / bound, and the iterations of the loops that run
most. Loop counts come from rerunning only that input with the loop heads
traced, so the batch itself runs untraced.

`gen.py` runs in a child process (`fuzz_mcp.py --gen GEN PER`), so nothing it
prints reaches the protocol.

The protocol is MCP over stdio: one JSON-RPC message per line.
"""
from __future__ import annotations
import json, random, runpy, subprocess, sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))       # fuzzing/
from steptrace import Runner, build  # first: it puts bigodafny/ on sys.path
from common import _in_spec

TOP = 5                                  # loops shown
TIMEOUT = 10                             # seconds per input
TOOL = {
    "name": "fuzz",
    "description": "Run gen.py's inputs on a .dfy file in your row directory; return a table of steps.",
    "inputSchema": {
        "type": "object",
        "properties": {
            "dfy": {"type": "string", "description": "absolute path of the .dfy file"},
            "gen": {"type": "string", "description": "absolute path of gen.py"},
            "per": {"type": "integer", "description": "inputs per family and grid point (default 3)"},
        },
        "required": ["dfy", "gen"],
    },
}


def generate(gen, per):
    """GRID, and every input gen.py makes: [grid index, family, text or None, error or None]."""
    g = runpy.run_path(gen)
    inputs = []
    for i, sizes in enumerate(g["GRID"]):
        for fam, f in g["FAMILIES"].items():
            for k in range(per):
                try:
                    text = f(random.Random(f"{i}/{fam}/{k}"), **sizes)
                    # Python's input() reads a last line without "\n"; BigOBench's parsers need it.
                    inputs.append([i, fam, text if text.endswith("\n") else text + "\n", None])
                except Exception as e:
                    inputs.append([i, fam, None, f"{fam} at {sizes}: {type(e).__name__}: {e}"[:300]])
    return g["GRID"], inputs


def fuzz(dfy, gen, per=3):
    sid = Path(dfy).parent.name
    p = subprocess.run([sys.executable, __file__, "--gen", gen, str(per)],
                       capture_output=True, text=True, timeout=600)
    if p.returncode:
        raise RuntimeError(f"gen.py failed:\n{p.stderr.strip()[-1000:]}")
    grid, inputs = json.loads(p.stdout.splitlines()[-1])        # gen.py's own prints come first
    r = Runner(sid, dfy=dfy)
    out = [f"note: {n}" for n in r.notes]

    statuses, broken, gen_error, parse_error, worst = Counter(), 0, None, None, [None] * len(grid)
    for i, fam, text, error in inputs:
        if error:
            res = {"status": "gen"}
            gen_error = gen_error or error
        else:
            res = r.run(text, timeout=TIMEOUT) if _in_spec(r.task, text) else {"status": "out-of-spec"}
        statuses[res["status"]] += 1
        if res["status"] == "parse":
            parse_error = parse_error or f"{fam}: {res['error']}"
        broken += res.get("bound_ok") is False
        if res["status"] == "ok" and (worst[i] is None or res["steps"] > worst[i][1]["steps"]):
            worst[i] = (fam, res, text)
    r.close()

    # Rerun each grid point's costliest input with only the loop heads traced.
    _, points, _, _ = build(sid, "", dfy)
    loops = [p for p in points if p["Kind"] == "loop"]
    hits, src = [{} for _ in worst], {}
    if loops and any(worst):
        rt = Runner(sid, trace=",".join(sorted({str(p["Line"]) for p in loops})), dfy=dfy)
        traced = [p for p in rt.points if p["Kind"] == "loop"]
        src = {p["Line"]: f"{p['Method']}: {p['src']}" for p in traced}
        for k, w in enumerate(worst):
            if w:
                res = rt.run(w[2], timeout=TIMEOUT * 10)
                h = {int(i): v[0] for i, v in res.get("hits", {}).items()} if res["status"] == "ok" else {}
                hits[k] = {p["Line"]: h.get(p["Id"], 0) for p in traced}
        rt.close()
    last = next((h for h in reversed(hits) if h), {})
    shown = sorted(last, key=lambda line: -last[line])[:TOP]

    out.append(f"{'k':>2}  {'sizes':<18} {'family':<10} {'steps':>10} {'bound':>12} {'ratio':>6}"
               + "".join(f" {'L' + str(line):>9}" for line in shown))
    for k, w in enumerate(worst):
        sizes = " ".join(f"{n}={v}" for n, v in grid[k].items())
        if not w:
            out.append(f"{k:>2}  {sizes:<18} {'-':<10} {'no ok run':>10}")
            continue
        fam, res, _ = w
        bound = res.get("bound")
        ratio = f"{res['steps'] / bound:.3f}" if bound else "-"
        out.append(f"{k:>2}  {sizes:<18} {fam:<10} {res['steps']:>10} "
                   f"{bound if bound is not None else '-':>12} {ratio:>6}"
                   + "".join(f" {hits[k].get(line, '-'):>9}" for line in shown))
    out += [f"  L{line:<4} {src[line]}" for line in shown]
    if len(last) > TOP:
        out.append(f"  ({len(last) - TOP} more loops not shown)")
    out.append(f"generated: {dict(statuses)}")
    if gen_error:
        out.append(f"first generator error: {gen_error}")
    if parse_error:
        out.append(f"first parse error: {parse_error}")
    if broken:
        out.append(f"BOUND BROKEN on {broken} generated inputs")
    return "\n".join(out)


def answer(msg):
    method = msg.get("method")
    if method == "initialize":
        return {"protocolVersion": msg["params"]["protocolVersion"],
                "capabilities": {"tools": {}}, "serverInfo": {"name": "fuzz", "version": "1"}}
    if method == "ping":
        return {}
    if method == "tools/list":
        return {"tools": [TOOL]}
    if method == "tools/call":
        try:
            text, failed = fuzz(**msg["params"]["arguments"]), False
        except Exception as e:
            text, failed = f"{type(e).__name__}: {e}", True
        return {"content": [{"type": "text", "text": text}], "isError": failed}
    return None


def main():
    for line in sys.stdin:
        msg = json.loads(line)
        if "id" not in msg:
            continue                                  # a notification: no reply
        result = answer(msg)
        reply = ({"result": result} if result is not None
                 else {"error": {"code": -32601, "message": f"no method {msg.get('method')}"}})
        sys.stdout.write(json.dumps({"jsonrpc": "2.0", "id": msg["id"], **reply}) + "\n")
        sys.stdout.flush()


if __name__ == "__main__":
    if sys.argv[1:2] == ["--gen"]:
        print(json.dumps(generate(sys.argv[2], int(sys.argv[3]))))
    else:
        main()
