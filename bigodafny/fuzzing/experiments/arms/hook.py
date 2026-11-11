"""The PreToolUse and Stop hook of the `arms-*` agents. Each arm's `guard.py` calls `main` with its rules.

On top of `prove_guard.py`, which this module runs unchanged on a stage of its own:

- `fuzz`: Bash may also run `fuzz.py <row>/row.dfy <row>/gen.py [--per N] [--bound 'E']` and Write may
  write `gen.py`, at most `MAX_FUZZ` calls, and only until `result.json` holds a guess.
- `guess_first`: Write and Edit of `proof.dfy` are denied until `result.json` holds `guess` and `guess_basis`.
- `push`: on Stop, `prove_guard.stop` decides (all 3 attempts unless `relation` is `confirms` or tighter).
  Without it, the agent may stop once `result.json` is complete and one attempt ran.
- Every arm: Stop is blocked until `class`, and `guess` in a `guess_first` arm, match `fuzz/guard.py`'s `CLASS`.
"""
from __future__ import annotations
import importlib.util, json, re, sys, time
from pathlib import Path

ARMS = Path(__file__).resolve().parent
FUZZING = ARMS.parents[1]
sys.path.insert(0, str(FUZZING.parents[1] / ".claude/skills/bigodafny-prove-campaign/scripts"))
import prove_guard as pg                                              # noqa: E402

# fuzz/guard.py has the same module name as each arm's guard.py, so load it by path
_spec = importlib.util.spec_from_file_location("fuzz_guard", FUZZING / "experiments/fuzz/guard.py")
fuzz_guard = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(fuzz_guard)

STAGE = Path.home() / ".cache" / "bigodafny-arms"                    # <arm>/<sid>/ per row
MAX_SECONDS, MAX_FUZZ, FUZZ_TIMEOUT_MS = 1800, 3, 600_000


def result(row):
    try:
        r = json.loads((row / "result.json").read_text())
        return r if isinstance(r, dict) else {}
    except (OSError, json.JSONDecodeError):
        return {}


def guessed(row):
    r = result(row)
    return bool(r.get("guess") and r.get("guess_basis"))


def in_row(agent, path):
    """AGENT's row, after checking PATH lies in it."""
    row = pg.locked_row(agent, path)
    if Path(path).resolve() != row and row not in Path(path).resolve().parents:
        raise pg.Denied(f"{path} is outside your directory {row}")
    return row


def check_fuzz(args, agent, m):
    row = in_row(agent, m["dfy"])
    if Path(m["dfy"]).resolve() != row / "row.dfy" or Path(m["gen"]).resolve() != row / "gen.py":
        raise pg.Denied("fuzz.py runs only on your row.dfy and gen.py")
    if args.get("run_in_background") or args.get("timeout", 0) < FUZZ_TIMEOUT_MS:
        raise pg.Denied(f"run fuzz.py in the foreground, with Bash timeout {FUZZ_TIMEOUT_MS}")
    budget = pg.read_budget(row)
    if pg.over_budget(budget):
        raise pg.Denied(f"the {MAX_SECONDS} s budget is spent: write result.json and stop")
    if guessed(row):
        raise pg.Denied("fuzz.py runs only before you write your guess")
    if budget.get("fuzz_calls", 0) >= MAX_FUZZ:
        raise pg.Denied(f"the {MAX_FUZZ} fuzz.py calls are spent: write your guess")
    pg.write_budget(row, {**budget, "fuzz_calls": budget.get("fuzz_calls", 0) + 1})


def check(tool, args, agent, fuzz, guess_first):
    """Return normally if the call is allowed."""
    if fuzz and tool == "Bash" and (m := fuzz_guard.FUZZ.fullmatch(args.get("command", "").strip())):
        return check_fuzz(args, agent, m)
    if tool in ("Write", "Edit") and "file_path" in args:
        path = Path(args["file_path"]).resolve()
        if fuzz and path.name == "gen.py":
            row = in_row(agent, path)
            if path != row / "gen.py" or guessed(row) or pg.over_budget(pg.read_budget(row)):
                raise pg.Denied("you may write gen.py only in your directory, before your guess")
            return
        if guess_first and path.name == "proof.dfy" and not guessed(in_row(agent, path)):
            raise pg.Denied("write guess and guess_basis to result.json before you edit proof.dfy")
    pg.check(tool, args, agent)


def class_error(row, guess_first):
    r = result(row)
    for key in ("class", "guess") if guess_first else ("class",):
        if not fuzz_guard.CLASS.fullmatch(str(r.get(key) or "")):
            return f"result.json: {key} must be written like O(nlogn), O(n**2) or O(n*m)"
    return None


def result_error(row, attempts):
    """The baseline's result.json check: fewer fields than prove_guard.result_error asks for."""
    r = result(row)
    if r.get("outcome") not in pg.OUTCOMES:
        return f"result.json: outcome must be one of {pg.OUTCOMES}"
    if not r.get("stop_reason"):
        return "result.json: stop_reason is empty"
    if r["outcome"] == "proved" and not r.get("bound"):
        return "result.json: a proved row needs bound"
    if r["outcome"] == "proved" and r.get("best_attempt") not in range(1, attempts + 1):
        return f"result.json: best_attempt must be an attempt from 1 to {attempts}"
    return None


def stop(agent, guess_first, push):
    row = pg.locked_row(agent)
    budget = pg.read_budget(row)
    why = class_error(row, guess_first)
    if why is None and push:
        return pg.stop(agent)
    if why is None:
        why = result_error(row, budget["attempts"])
    if why is None and budget["attempts"] == 0 and not pg.over_budget(budget):
        why = "make at least one verify attempt"
    if why is None or budget.get("stops", 0) >= pg.TRIES:
        pg.write_budget(row, {**budget, "ended": time.time(), "stop_error": why})
        return
    pg.write_budget(row, {**budget, "stops": budget.get("stops", 0) + 1})
    raise pg.Denied(f"do not stop yet: {why}")


def main(arm, fuzz, guess_first, push):
    pg.ROOT, pg.MAX_SECONDS = STAGE / arm, MAX_SECONDS
    payload = {}
    try:
        payload = json.load(sys.stdin)
        agent = re.sub(r"\W", "_", str(payload["agent_id"]))
        tool = payload.get("tool_name")
        if payload.get("hook_event_name") == "SubagentStop" or tool == "SubagentHandback":
            stop(agent, guess_first, push)
        else:
            check(tool, payload.get("tool_input") or {}, agent, fuzz, guess_first)
    except Exception as e:                       # a broken guard must deny, never allow
        pg.log(payload, f"{type(e).__name__}: {e}")
        print(f"DENIED: {e}", file=sys.stderr)
        sys.exit(2)
