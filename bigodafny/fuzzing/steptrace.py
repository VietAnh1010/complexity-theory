"""Run a proof copy with its ghost step counter compiled; record `steps` at program points.

A proof in `solutions-proved/` counts work in a ghost `steps`, which compilation
erases. The `DafnySteps` plugin (`DafnySteps/Deghost.cs`) makes the counter and
everything flowing into it compiled, on Dafny's own AST, before resolution;
`Solve` then returns `(output, steps)`.

With `--trace`, the plugin also inserts `print <point>, steps;` after each
assignment to `steps` and at each loop head; the harness captures those prints.
Points are listed in `points.json` by line and column of the proof's source.
`--trace LINE,..` inserts points on those source lines only; an unselected
point costs nothing at run time.

The plugin also compiles Solve's contract: `TraceRequires` rejects an input
the proof does not cover; `TraceBound`, present when Solve has an `ensures`,
checks each run against every `ensures`, the step bound among them; `TraceBoundValue` gives the bound's
value, so `steps / bound` shows how tight it is. A run over its proved bound means the
compiled counter does not count what the proof counts. If the contract does
not compile (a ghost-only predicate), the build is retried without it.

`DafnySteps deghost` prints the program the plugin compiles, for reading.
"""
from __future__ import annotations
import argparse, json, subprocess, sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from common import (BUILD, DATA, OUT, PROVED, PROVED_VALUE, log, read_jsonl,
                    spec_tests, write_jsonl)
from validate import conv_expr

TOOL = Path(__file__).resolve().parent / "DafnySteps"
BIN = TOOL / "bin" / "Release" / "net10.0"       # the CLI `DafnySteps` and the plugin's DLL
DLL = BIN / "DafnySteps.dll"
COUNTER = "steps"                                # the counter's name unless one is given
TIERS = ("public_tests", "private_tests", "generated_tests")


def find_proof(sid):
    pid = sid.split("_")[0]
    for root in (PROVED, PROVED_VALUE):
        if (root / pid / f"{sid}.dfy").exists():
            return root / pid / f"{sid}.dfy"
    raise SystemExit(f"{sid}: no proof copy in solutions-proved/")


def plugin():
    """The plugin DLL, built if missing."""
    if not DLL.exists():
        subprocess.run(["dotnet", "build", "-c", "Release", str(TOOL)], check=True,
                       capture_output=True)
    return DLL


def build(sid, trace=None, dfy=None, counter=COUNTER):
    """Compile `dfy` (default: the row's proof copy) with the counter compiled.
    `trace`: None, "all", "loops" or "LINE,..". -> (pydir, points, notes)."""
    other = dfy is not None
    dfy = Path(dfy) if other else find_proof(sid)
    work = BUILD / f"trace_{sid}{'' if trace is None else '_t'}{'_file_' + dfy.stem if other else ''}"
    work.mkdir(parents=True, exist_ok=True)
    points_path = work / "points.json"
    notes = []
    for contracts in (True, False):
        args = [f"counter={counter}", f"points={points_path}"]
        if trace == "all":
            args.append("trace")
        elif trace is not None:
            args.append(f"trace={trace}")
        if contracts:
            args.append("contracts")
        p = subprocess.run(["dafny", "translate", "py", str(dfy), "--no-verify",
                            "--include-runtime", "--output", str(work / "out"),
                            "--plugin", f"{plugin()},{' '.join(args)}"],
                           capture_output=True, text=True, timeout=300)
        if p.returncode == 0 and (work / "out-py" / "module_.py").exists():
            points = [] if trace is None else json.loads(points_path.read_text())
            src = dfy.read_text(encoding="utf-8").split("\n")
            for pt in points:
                pt["src"] = src[pt["Line"] - 1].strip()[:80]
            return work / "out-py", points, notes
        notes.append(f"build {'with' if contracts else 'without'} contracts failed: "
                     + (p.stdout + p.stderr).strip()[-400:])
    raise RuntimeError(f"{sid}: cannot compile the counter:\n" + "\n".join(notes))


HARNESS = '''\
"""Generated. One line of JSON in, one out: {{"input": text}} -> steps and hits."""
import json, signal, sys
from fractions import Fraction
sys.path.insert(0, {pydir!r})
sys.setrecursionlimit(100000)
import _dafny
from module_ import default__ as row    # Dafny compiles the row's top-level methods into this class

def _mkreal(x):
    f = Fraction(x).limit_denominator(10 ** 12)
    return _dafny.BigRational(f.numerator, f.denominator)


_ns = {{}}
exec(compile(open({dcpath!r}, encoding="utf-8").read(), "dataclass", "exec"), _ns)
Input = _ns["Input"]
hits, pending = {{}}, []


def _print(v):
    """A trace point prints its id, then steps: two calls."""
    if pending:
        _hit(pending.pop(), v)
    else:
        pending.append(v)


def _hit(pid, s):
    h = hits.get(pid)
    if h is None:
        hits[pid] = h = [0, s, s, s]
    h[0] += 1
    h[3] = s
    if s < h[1]: h[1] = s
    if s > h[2]: h[2] = s


_dafny.print = _print         # the only prints in the copy are trace points
_dafny.string_of = lambda v: v


class _Timeout(Exception):
    pass


class _Unparsed(Exception):
    pass


def _alarm(signum, frame):
    raise _Timeout()


signal.signal(signal.SIGALRM, _alarm)
for line in sys.stdin:
    req = json.loads(line)
    hits.clear(); pending.clear()
    res = {{}}
    signal.alarm(req.get("timeout", 30))
    try:
        try:
            inp = Input.from_str(req["input"])
        except Exception as e:
            raise _Unparsed(e)
        if hasattr(row, "TraceRequires") and not row.TraceRequires({args}):
            res = {{"status": "requires"}}
        else:
            outs = row.Solve({args})
            steps = outs[1]
            res = {{"status": "ok", "steps": int(steps), "output_len": len(outs[0]),
                    "hits": {{str(k): v for k, v in hits.items()}}}}
            if hasattr(row, "TraceBound"):
                hits.clear()            # TraceBound's prints are not hits of this run
                res["bound_ok"] = bool(row.TraceBound({args}, *outs))
                if hasattr(row, "TraceBoundValue"):
                    res["bound"] = int(row.TraceBoundValue({args}, *outs))
    except _Timeout:
        res = {{"status": "timeout"}}
    except _Unparsed as e:
        res = {{"status": "parse", "error": f"{{type(e.args[0]).__name__}}: {{e.args[0]}}"[:300]}}
    except Exception as e:
        res = {{"status": "error", "error": f"{{type(e).__name__}}: {{e}}"[:300]}}
    finally:
        signal.alarm(0)
    sys.stdout.write(json.dumps(res) + "\\n")
    sys.stdout.flush()
'''


class Runner:
    """A long-lived Python process running one row's counter on input texts."""

    def __init__(self, sid, trace=None, dfy=None, counter=COUNTER):
        self.sid = sid
        self.task = next(t for t in read_jsonl(DATA / "tasks.jsonl") if t["solution_id"] == sid)
        sig = next(s for s in read_jsonl(DATA / "signatures.jsonl")
                   if s["problem_id"] == self.task["problem_id"])
        pydir, self.points, self.notes = build(sid, trace, dfy, counter)
        work = pydir.parent
        (work / "dataclass.py").write_text(self.task["dataclass_code"], encoding="utf-8")
        args = ", ".join(conv_expr(p["dafny_type"], f'inp.{p["py_name"]}')
                         for p in sig["params"])
        (work / "harness.py").write_text(HARNESS.format(
            pydir=str(pydir), dcpath=str(work / "dataclass.py"),
            args=args), encoding="utf-8")
        self.proc = subprocess.Popen([sys.executable, str(work / "harness.py")],
                                     stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                     text=True, bufsize=1)

    def run(self, text, timeout=30):
        self.proc.stdin.write(json.dumps({"input": text, "timeout": timeout}) + "\n")
        line = self.proc.stdout.readline()
        if not line:
            raise RuntimeError(f"{self.sid}: harness died")
        return json.loads(line)

    def seeds(self):
        """The row's stored test inputs that keep the problem's stated limits."""
        return [t["input"] for _, t in spec_tests(self.task, TIERS)[0]]

    def close(self):
        self.proc.stdin.close()
        self.proc.wait()


def report(runner, res):
    """Per-point table: hits, and steps at the first and last hit."""
    rows = []
    for pt in sorted(runner.points, key=lambda p: (p["Line"], p["Col"])):
        hits, low, high, last = res.get("hits", {}).get(str(pt["Id"]), (0, None, None, None))
        rows.append({**pt, "hits": hits, "min": low, "max": high, "last": last})
    return rows


def main(argv=None):
    ap = argparse.ArgumentParser(prog="steptrace.py")
    ap.add_argument("sid")
    ap.add_argument("--input", help="file holding one input text (default: the row's tests)")
    ap.add_argument("--dfy", help="the .dfy to run (default: the row's proof copy)")
    ap.add_argument("--trace", nargs="?", const="all", metavar="all|loops|LINE,..",
                    help="record steps at each program point, only at loop heads, or only on these source lines")
    ap.add_argument("--counter", default=COUNTER, help="the counter's name in the .dfy")
    a = ap.parse_args(argv)
    r = Runner(a.sid, trace=a.trace, dfy=a.dfy, counter=a.counter)
    for n in r.notes:
        log(f"{a.sid}: {n}")
    texts = [Path(a.input).read_text()] if a.input else r.seeds()
    recs = []
    for k, text in enumerate(texts):
        res = r.run(text)
        rec = {"solution_id": a.sid, "test": k, "input_len": len(text), **res}
        if a.trace is not None and res["status"] == "ok":
            rec["points"] = report(r, res)
            del rec["hits"]
        recs.append(rec)
        print(f"test {k:>3}  {res['status']:<8} steps={res.get('steps')}  "
              f"input_len={len(text)}  bound={res.get('bound', '-')}  bound_ok={res.get('bound_ok', '-')}")
    r.close()
    if recs and recs[-1].get("points"):
        print(f"\npoints, last test ({len(texts[-1])} chars):")
        for p in recs[-1]["points"]:
            print(f"  L{p['Line']:<4} {p['Kind']:<6} hits={p['hits']:<7} "
                  f"steps {p['min']}..{p['max']}  {p['src']}")
    write_jsonl(OUT / "trace" / f"{a.sid}.jsonl", recs)
    log(f"{Counter(x['status'] for x in recs)}; bound broken on "
        f"{sum(x.get('bound_ok') is False for x in recs)} -> out/trace/{a.sid}.jsonl")
    return 0


if __name__ == "__main__":
    sys.exit(main())
