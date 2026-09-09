"""Recover each agent's trajectory from its own transcript.

The Agent tool returns only a final report, which is the agent's account of
itself. The transcripts are the record: one JSONL per subagent under
`<project>/<session>/subagents/`, with a timestamp and the full input on every
tool call, plus a `.meta.json` naming the model. This project's rule is to audit
every agent batch from scratch rather than trust its count, and that rule needs
primary evidence.

Two jobs:

  * trajectory -- tool calls, dafny invocations, wall time, tokens, per example.
    Agents work through a batch in order, so a call is attributed to the last
    example id mentioned; calls before any id are `shared` setup.
  * leak audit -- did a blind agent reach for the answer. This is the
    detection half of the anti-cheat; `guard.py` is the prevention half. Both
    are reported: an attempt that the guard denied is still a datum about the
    agent, and a run with attempts is a run whose accuracy needs an asterisk.

    python3 experiments/harvest.py --run-id pilot1 --snapshot   # before a wave
    python3 experiments/harvest.py --run-id pilot1              # after it
"""
from __future__ import annotations
import argparse, json, re, sys
from collections import Counter, defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
RUNS = HERE / "runs"
PROJ = Path("/root/.claude/projects/-home-user-complexity-theory")

# Anything under here would hand a blind agent the label directly.
BANNED = [
    (re.compile(r"solutions(-\w+)?/"), "repo solutions tree"),
    (re.compile(r"tasks\.jsonl|dataset\.jsonl|stats\.json|validation"), "dataset files"),
    (re.compile(r"COMPLEXITY\.md|STATUS\.md|summaries/|README\.md"), "project notes"),
    (re.compile(r"\.claude/skills|bigodafny[- ]"), "project skills"),
    (re.compile(r"\bgit\s+(log|show|diff|grep|blame)"), "git history"),
    # Anchored at the repo root on purpose. The scratchpad these examples are
    # staged in is itself named `-home-user-complexity-theory`, so an
    # unanchored `complexity-theory/` flags every legitimate call an agent
    # makes in its own directory. It did: 21 of the pilot's 23 "leaks".
    (re.compile(r"/home/user/complexity-theory(?!.*cx-run)"), "repo path"),
    (re.compile(r"time_complexity"), "the label field itself"),
]
SID_RE = re.compile(r"\b(\d{1,5}_\d{1,5})\b")


def subagent_dir():
    cands = [p / "subagents" for p in PROJ.iterdir()
             if p.is_dir() and (p / "subagents").is_dir()]
    if not cands:
        sys.exit(f"no subagents directory under {PROJ}")
    return max(cands, key=lambda p: p.stat().st_mtime)


def tool_calls(path: Path):
    out, prompt, tokens = [], "", 0
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        if not line.strip():
            continue
        try:
            r = json.loads(line)
        except Exception:
            continue
        msg = r.get("message") or {}
        if r.get("type") == "user" and not prompt:
            c = msg if isinstance(msg, str) else msg.get("content")
            prompt = c if isinstance(c, str) else json.dumps(c)[:20000]
        tokens += (msg.get("usage") or {}).get("output_tokens", 0) or 0
        content = msg.get("content")
        if not isinstance(content, list):
            continue
        for b in content:
            if isinstance(b, dict) and b.get("type") == "tool_use":
                out.append({"ts": r.get("timestamp"), "tool": b.get("name"),
                            "input": json.dumps(b.get("input"))[:4000]})
    return prompt, out, tokens


def secs(a, b):
    from datetime import datetime
    try:
        f = "%Y-%m-%dT%H:%M:%S.%fZ"
        return round((datetime.strptime(b, f) - datetime.strptime(a, f)).total_seconds(), 1)
    except Exception:
        return None


def harvest_agent(jsonl: Path, known_sids, run_id):
    meta_p = jsonl.with_suffix(".meta.json")
    meta = json.loads(meta_p.read_text()) if meta_p.exists() else {}
    prompt, calls, tokens = tool_calls(jsonl)
    # An agent belongs to this run iff its prompt names the run's staged root.
    # Snapshot-and-diff was the first design and it silently lost the pilot's
    # blind agent: a second snapshot taken before harvesting recorded that
    # agent's transcript as pre-existing. Matching on the path cannot do that.
    if f"cx-run/{run_id}/" not in prompt or "result.json" not in prompt:
        return None      # not an experiment batch -- e.g. a guard-hook probe
    mine = [s for s in dict.fromkeys(SID_RE.findall(prompt)) if s in known_sids]

    per = defaultdict(lambda: {"calls": [], "leaks": []})
    cur = "shared"
    for c in calls:
        hit = [s for s in SID_RE.findall(c["input"]) if s in known_sids]
        if hit:
            cur = hit[0]
        per[cur]["calls"].append(c)
        for rx, why in BANNED:
            if rx.search(c["input"]):
                per[cur]["leaks"].append({"why": why, "tool": c["tool"],
                                          "ts": c["ts"], "input": c["input"][:300]})
                break

    arm = ("labeled" if f"cx-run/{run_id}/labeled/" in prompt
           else "blind" if f"cx-run/{run_id}/blind/" in prompt else "?")
    out = {"agent_id": jsonl.stem, "model": meta.get("model"), "arm": arm,
           "description": meta.get("description"), "sids": mine,
           "output_tokens": tokens, "tool_calls": len(calls),
           "wall_s": secs(calls[0]["ts"], calls[-1]["ts"]) if len(calls) > 1 else 0,
           "per_example": {}}
    for sid, d in per.items():
        cs = d["calls"]
        out["per_example"][sid] = {
            "tool_calls": len(cs),
            "dafny_calls": sum(1 for c in cs if "dafny" in c["input"]),
            "tools": dict(Counter(c["tool"] for c in cs)),
            "wall_s": secs(cs[0]["ts"], cs[-1]["ts"]) if len(cs) > 1 else 0,
            "leak_attempts": len(d["leaks"]),
            "leaks": d["leaks"][:5],
        }
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--run-id", required=True)
    ap.add_argument("--snapshot", action="store_true",
                    help="deprecated no-op; agents are matched by the run root "
                         "named in their prompt, so no snapshot is needed")
    ap.add_argument("--tag", default="wave")
    a = ap.parse_args()

    d = subagent_dir()
    rd = RUNS / a.run_id
    rd.mkdir(parents=True, exist_ok=True)
    snap = rd / "agents_before.json"

    names = sorted(p.name for p in d.glob("agent-*.jsonl"))
    if a.snapshot:
        print("--snapshot is a no-op; agents are matched by run root in prompt")
        return

    man = json.loads((HERE / "manifest.json").read_text())
    known = {e["sid"] for e in man["examples"]}

    agents = [harvest_agent(d / n, known, a.run_id) for n in names]
    agents = [x for x in agents if x and x["sids"]]
    # Rewrite what is present, PRESERVE what is gone.
    #
    # This was a full rewrite, on the reasoning that matching is deterministic
    # so the file should hold exactly the agents that match, and a merge would
    # keep entries an earlier looser rule let in. The reasoning holds only if
    # every transcript is still on disk. They are not: transcripts live in a
    # per-session temp directory, so running this in a later session scanned 4
    # transcripts, matched 2, and silently cut trajectory.json from 16 agents
    # to 2 -- every earlier wave's tool counts, dafny calls and leak audit,
    # gone, with `difficulty_measured` quietly falling back to a default.
    #
    # So: an agent whose transcript is present is re-derived under the current
    # rule, exactly as before. An agent whose transcript is absent is kept and
    # marked, because it cannot be re-derived and dropping it is data loss, not
    # hygiene. The marker is what keeps that honest -- a preserved entry is a
    # claim about a run this invocation could not check.
    p = rd / "trajectory.json"
    byid = {}
    if p.exists():
        for x in json.loads(p.read_text(encoding="utf-8")):
            x["transcript_absent"] = True
            byid[x["agent_id"]] = x
    preserved = set(byid) - {x["agent_id"] for x in agents}
    for x in agents:
        x["transcript_absent"] = False
        byid[x["agent_id"]] = x
    p.write_text(json.dumps(sorted(byid.values(), key=lambda x: x["agent_id"]),
                            indent=1, sort_keys=True), encoding="utf-8")

    leaks = sum(v["leak_attempts"] for x in byid.values()
                for v in x["per_example"].values())
    print(f"transcripts scanned: {len(names)}, belonging to this run: {len(agents)}")
    print(f"trajectory -> {p}  ({len(byid)} agents: "
          f"{len(agents)} re-derived, {len(preserved)} preserved from earlier "
          f"sessions whose transcripts are gone)")
    print(f"leak attempts recorded: {leaks}")
    for x in byid.values():
        for sid, v in x["per_example"].items():
            for lk in v["leaks"]:
                print(f"  LEAK {x['agent_id'][:14]} {sid:10} {lk['why']:22} "
                      f"{lk['tool']}: {lk['input'][:90]}")


if __name__ == "__main__":
    main()
