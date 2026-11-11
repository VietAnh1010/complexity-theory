#!/usr/bin/env python3
"""PreToolUse and Stop hook of the `prove-blind` agent (`.claude/agents/prove-blind.md`).

Keeps each agent in its stage directory, so it cannot see an existing proof, and
enforces the budget. Any error denies the call.

- An agent is locked to the row directory of the first path it names.
- Read and Grep: the agent's row directory and the stage's `prelude.dfy`.
- Write and Edit: only the row's `proof.dfy` and `result.json`.
- Bash: only `dafny verify <row>/proof.dfy --verification-time-limit 30`, in the
  foreground, on a `proof.dfy` that differs from `row.dfy` and the last attempt. Each
  run counts as an attempt and snapshots `attempts/<n>.dfy`.
- Past the clock, only `result.json` stays open.
- Stop and the hand-back tool are blocked up to TRIES times until `result.json` is complete and, unless the
  clock has run out, the agent has made an attempt. An agent must use all its attempts
  unless it claims a bound at or below the label. A stop let through after TRIES blocks
  records its reason as `stop_error`.

Denials go to `<stage>/guard.log`. A denial means the agent saw nothing, so it
does not void the row. `budget.json` in the row holds the measured attempts and seconds.
"""
from __future__ import annotations
import json, re, shutil, sys, time
from pathlib import Path

ROOT = Path.home() / ".cache" / "bigodafny-stage"
MAX_ATTEMPTS, MAX_SECONDS, MIN_BASH_TIMEOUT_MS, TRIES = 3, 900, 300_000, 3
VERIFY = re.compile(r"dafny verify (?P<path>/[\w./-]+/proof\.dfy) --verification-time-limit 30")
OUTCOMES = ("proved", "unresolved")
OBSTACLES = ("z3-nonlinear", "math-too-hard", "invariant-gap", "termination-not-proved", "other")
EARLY_STOP = ("confirms", "tighter-costmodel", "tighter-translation", "tighter-label")   # at or below the label


class Denied(Exception):
    pass


def read_budget(row):
    return json.loads((row / "budget.json").read_text())


def write_budget(row, budget):
    (row / "budget.json").write_text(json.dumps(budget))


def row_of(path):
    """The row directory (holding BRIEF.md) at or above PATH, under ROOT."""
    p = Path(path).resolve()
    for d in [p, *p.parents]:
        if d == ROOT or ROOT not in d.parents:
            return None
        if (d / "BRIEF.md").exists():
            return d
    return None


def locked_row(agent, path=None):
    """The row AGENT is locked to; PATH locks a new agent to PATH's row."""
    lock = ROOT / ".locks" / agent
    if lock.exists():
        return Path(lock.read_text())
    row = row_of(path) if path else None
    if row is None:
        raise Denied("work inside your row directory, named in your prompt")
    lock.parent.mkdir(exist_ok=True)
    lock.write_text(str(row))
    write_budget(row, {**read_budget(row), "started": time.time()})
    return row


def over_budget(budget):
    return time.time() - budget["started"] > MAX_SECONDS


def path_arg(tool, args):
    if tool == "Bash":
        if args.get("run_in_background"):
            raise Denied("run dafny verify in the foreground")
        m = VERIFY.fullmatch(args.get("command", "").strip())
        if not m:
            raise Denied("Bash runs only `dafny verify <your dir>/proof.dfy --verification-time-limit 30`")
        if args.get("timeout", 0) < MIN_BASH_TIMEOUT_MS:
            raise Denied(f"call Bash with timeout {MIN_BASH_TIMEOUT_MS}")
        return m["path"]
    key = "file_path" if tool in ("Read", "Write", "Edit") else "path"
    if key not in args:
        raise Denied(f"give `{key}` under your directory")
    return args[key]


def check(tool, args, agent):
    """Return normally if the call is allowed."""
    if tool == "SubagentHandback":                                    # also ends the agent: same check as Stop
        stop(agent)
        return
    if tool not in ("Read", "Grep", "Write", "Edit", "Bash"):
        raise Denied(f"{tool} is not available")
    path = path_arg(tool, args)
    resolved = Path(path).resolve()
    if tool in ("Read", "Grep") and resolved == ROOT / "prelude.dfy":
        locked_row(agent)                                             # a new agent opens its row first
        return
    row = locked_row(agent, path)
    if row != resolved and row not in resolved.parents:
        raise Denied(f"{path} is outside your directory {row}")
    budget = read_budget(row)
    if resolved == row / "result.json" and tool != "Grep":
        return
    if over_budget(budget):
        raise Denied(f"the {MAX_SECONDS} s budget is spent: write result.json and stop")
    if tool in ("Write", "Edit") and resolved != row / "proof.dfy":
        raise Denied("you may write only proof.dfy and result.json")
    if tool == "Bash":
        if resolved != row / "proof.dfy":
            raise Denied("verify your own proof.dfy")
        if budget["attempts"] >= MAX_ATTEMPTS:
            raise Denied(f"the {MAX_ATTEMPTS} attempts are spent: write result.json and stop")
        last = row / "attempts" / f"{budget['attempts']}.dfy"
        proof = (row / "proof.dfy").read_bytes()
        if proof == (row / "row.dfy").read_bytes() or (last.exists() and proof == last.read_bytes()):
            raise Denied("proof.dfy has not changed: make a real proof attempt first")
        budget["attempts"] += 1
        shutil.copy(row / "proof.dfy", row / "attempts" / f"{budget['attempts']}.dfy")
        write_budget(row, budget)


def result_error(row, attempts):
    """None if ROW/result.json is complete, else what is wrong."""
    try:
        r = json.loads((row / "result.json").read_text())
    except (OSError, json.JSONDecodeError) as e:
        return f"result.json: {e}"
    if not isinstance(r, dict) or r.get("outcome") not in OUTCOMES:
        return f"result.json: outcome must be one of {OUTCOMES}"
    if not r.get("reads"):
        return "result.json: reads is empty"
    if not r.get("stop_reason"):
        return "result.json: stop_reason is empty"
    if r["outcome"] == "proved" and not (r.get("bound") and r.get("relation")):
        return "result.json: a proved row needs bound and relation"
    if r["outcome"] == "proved" and r.get("best_attempt") not in range(1, attempts + 1):
        return f"result.json: best_attempt must be an attempt from 1 to {attempts}"
    if r["outcome"] == "unresolved" and not (r.get("why_failed") and r.get("obstacle") in OBSTACLES):
        return f"result.json: an unresolved row needs why_failed and obstacle in {OBSTACLES}"
    return None


def stop(agent):
    """Let the agent stop once result.json is complete; block it up to TRIES times."""
    row = locked_row(agent)
    budget = read_budget(row)
    why = result_error(row, budget["attempts"])
    if why is None and not over_budget(budget):
        r = json.loads((row / "result.json").read_text())
        done = r["outcome"] == "proved" and r["relation"] in EARLY_STOP
        if budget["attempts"] == 0 or (not done and budget["attempts"] < MAX_ATTEMPTS):
            why = f"you have used {budget['attempts']} of {MAX_ATTEMPTS} attempts: keep trying for a tighter proof"
    if why is None or budget.get("stops", 0) >= TRIES:
        write_budget(row, {**budget, "ended": time.time(), "stop_error": why})
        return
    write_budget(row, {**budget, "stops": budget.get("stops", 0) + 1})
    raise Denied(f"do not stop yet: {why}")


def log(payload, why):
    if not ROOT.is_dir():
        return
    with (ROOT / "guard.log").open("a", encoding="utf-8") as fh:
        fh.write(json.dumps({"ts": time.strftime("%Y-%m-%dT%H:%M:%S"),
                             "agent": str(payload.get("agent_id"))[:24],
                             "tool": payload.get("tool_name") or payload.get("hook_event_name"),
                             "why": why, "input": json.dumps(payload.get("tool_input"))[:600]}) + "\n")


def main():
    payload = {}
    try:
        payload = json.load(sys.stdin)
        agent = re.sub(r"\W", "_", str(payload["agent_id"]))
        if payload.get("hook_event_name") == "SubagentStop":
            stop(agent)
        else:
            check(payload.get("tool_name"), payload.get("tool_input") or {}, agent)
    except Exception as e:                       # a broken guard must deny, never allow
        log(payload, f"{type(e).__name__}: {e}")
        print(f"DENIED: {e}", file=sys.stderr)
        sys.exit(2)


if __name__ == "__main__":
    main()
