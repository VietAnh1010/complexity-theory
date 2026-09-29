#!/usr/bin/env python3
"""Check a prove campaign's trajectories against the verifier, not the reports.

Run `python3 proofs.py` first -- it re-verifies every file in
`solutions-proved/` from scratch and writes `data/complexity_proofs.jsonl`.
This script joins that output to the campaign's manifest and trajectories and
reports every place they disagree.

    python3 audit.py --batch batches/prove-sample-2 --repo .

An agent's own report is not evidence. In the first campaign one agent's prose
said 9 proved where its trajectory said 10, and the files said 10.
"""

import argparse
import glob
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor

RELATIONS = {
    "confirms",
    "looser-slack",
    "looser-structural",
    "tighter-costmodel",
    "tighter-translation",
    "contradicts",
    None,
}

OBSTACLES = {
    "value-to-size",
    "z3-nonlinear",
    "invariant-gap",
    "decreases-star",
    "prelude-gap",
    "recursion-depth",
    "budget",
    "label-mismatch",
    "structural-unbounded",
}


def read_jsonl(path):
    if not os.path.exists(path):
        return []
    with open(path) as fh:
        return [json.loads(l) for l in fh if l.strip()]


def jsonl_problems(path):
    """One JSON object per line, or say which line breaks that.

    prove-sample-5's slice C wrote pretty-printed JSON spanning 59 lines for
    16 rows. Every consumer of the file raised instead of reporting, so the
    trajectory looked lost when it was only misformatted.
    """
    if not os.path.exists(path):
        return [f"{os.path.basename(path)}: missing"]
    out = []
    with open(path) as fh:
        for i, line in enumerate(fh, 1):
            if not line.strip():
                continue
            try:
                json.loads(line)
            except json.JSONDecodeError as exc:
                out.append(f"{os.path.basename(path)}:{i}: not one JSON object "
                           f"per line ({exc.msg})")
                break
    return out


DAFNY = shutil.which("dafny") or "/root/.dotnet/tools/dafny"


def emitted_python(repo, path):
    """The Python `dafny translate py` emits for the file's own module.

    Ghost code is erased, so a proof that only adds annotations emits the same
    Python as its row; compare through normalise(). Cached under
    .cache/emitted_py/ by the file's and the prelude's content. Returns
    (text, None) or (None, error).
    """
    with open(path, "rb") as fh:
        src = fh.read()
    with open(os.path.join(repo, "prelude.dfy"), "rb") as fh:
        pre = fh.read()
    key = hashlib.sha256(src + b"\0" + pre).hexdigest()
    cache = os.path.join(repo, ".cache", "emitted_py", key + ".py")
    if os.path.exists(cache):
        with open(cache) as fh:
            return fh.read(), None
    with tempfile.TemporaryDirectory() as tmp:
        out = os.path.join(tmp, "m")
        # --no-verify: proofs.py is the verifier; translating under load must
        # not turn a solver timeout into a failed identity check
        r = subprocess.run([DAFNY, "translate", "py", path, "--no-verify",
                            "--output", out],
                           capture_output=True, text=True, timeout=600)
        mod = out + "-py/module_.py"
        if r.returncode != 0 or not os.path.exists(mod):
            return None, (r.stdout + r.stderr).strip().splitlines()[-1:]
        with open(mod) as fh:
            text = fh.read()
    os.makedirs(os.path.dirname(cache), exist_ok=True)
    with open(cache, "w") as fh:
        fh.write(text)
    return text, None


def normalise(py):
    """Erase what a proof can change in emitted Python without changing code.

    * local names: `d_4_steps_` -> `d_4`. Renaming a local is not a change;
      renumbering is, since Dafny numbers locals in declaration order.
    * `elif True: pass`: an `else` branch that held only ghost code.
    * `d_7: int = int(0)`: the default a declaration gets when Dafny cannot
      see a definite assignment. Every read still follows a real assignment.
    * method order: Dafny emits methods in source order.
    """
    py = re.sub(r"\bd_(\d+)_\w*", r"d_\1", py)
    py = re.sub(r"\n([ \t]*)elif True:\n\1[ \t]+pass(?=\n)", "", py)
    py = re.sub(r"(?m)^([ \t]*d_\d+: [^=\n]+?) = .+$", r"\1", py)
    head, *methods = py.split("\n    @staticmethod\n")
    return head + "".join(sorted("\n    @staticmethod\n" + m.rstrip() + "\n"
                                 for m in methods))


def source_row(repo, sid, m):
    """The row as translated: the manifest's path, or wherever it moved since."""
    if m.get("path") and os.path.exists(os.path.join(repo, m["path"])):
        return os.path.join(repo, m["path"])
    pid = sid.split("_")[0]
    for root in sorted(glob.glob(os.path.join(repo, "solutions*"))):
        if os.path.basename(root) == "solutions-proved":
            continue
        cand = os.path.join(root, pid, f"{sid}.dfy")
        if os.path.exists(cand):
            return cand
    return None


def contracts(text):
    """{name: sorted requires clauses} for each method/function declared."""
    text = re.sub(r"//[^\n]*", "", text)
    out = {}
    for d in re.finditer(r"\b(?:method|function|predicate)\s+(?:\{[^}]*\}\s*)?(\w+)", text):
        # the header runs to the body's opening brace (not an attribute's)
        m = re.search(r"\{(?!:)", text[d.end():])
        header = text[d.end():d.end() + m.start()] if m else ""
        parts = re.split(r"\b(requires|ensures|decreases|reads|modifies)\b", header)
        out[d.group(1)] = sorted(" ".join(parts[i + 1].split())
                                 for i in range(1, len(parts) - 1, 2)
                                 if parts[i] == "requires")
    return out


def contract_changes(repo, sid, m, proof):
    """Row methods/functions whose `requires` the proof changed."""
    src = source_row(repo, sid, m)
    if src is None:
        return []
    with open(src) as fh:
        row = contracts(fh.read())
    with open(proof) as fh:
        prf = contracts(fh.read())
    return sorted(n for n in row if n in prf and row[n] != prf[n])


def identity(repo, sid, m, proof):
    """'identical', 'differs', or 'error: ...' for one row's proof."""
    src = source_row(repo, sid, m)
    if src is None:
        return "error: source row not found"
    a, ea = emitted_python(repo, src)
    b, eb = emitted_python(repo, proof)
    if ea or eb:
        return f"error: translate failed ({'row' if ea else 'proof'}): {ea or eb}"
    return "identical" if normalise(a) == normalise(b) else "differs"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--batch", required=True)
    ap.add_argument("--repo", default=".")
    args = ap.parse_args()

    manifest = {r["solution_id"]: r for r in read_jsonl(f"{args.batch}/manifest.jsonl")}
    traj = {}
    for name in sorted(os.listdir(args.batch)):
        if name.startswith("traj_") and name.endswith(".jsonl"):
            for row in read_jsonl(os.path.join(args.batch, name)):
                row["_slice"] = name[5:-6]
                traj[row["solution_id"]] = row

    proofs = {
        r["solution_id"]: r
        for r in read_jsonl(os.path.join(args.repo, "data/complexity_proofs.jsonl"))
    }
    # Once the relations have been normalised by hand, that file is the
    # authority; the agents' own values survive inside it as agent_said_*.
    normalised = {
        r["solution_id"]: r
        for r in read_jsonl(f"{args.batch}/label_relation.jsonl")
    }
    for sid, row in normalised.items():
        # a rerun record's relation is about the rerun's own proof, not the
        # proof label_relation.jsonl describes
        if sid in traj and not traj[sid].get("rerun"):
            traj[sid]["relation"] = row.get("relation")
            traj[sid]["relation_reason"] = row.get("reason", "")

    # A rerun proves each row afresh in rerun/<pid>/<sid>.dfy, away from the
    # overlay, and rerun/verify.jsonl is the verifier's result on those files
    # until they are promoted (a normalised batch has neither).
    # An existing overlay proof is deliberately NOT consulted for a rerun row:
    # the retry must not use it, so "unresolved while a proof exists" is the
    # expected case there, listed rather than failed.
    rerun_verify = {
        r["solution_id"]: r
        for r in read_jsonl(f"{args.batch}/rerun/verify.jsonl")
    } if os.path.exists(f"{args.batch}/rerun/verify.jsonl") else {}
    not_used, not_promoted = [], []

    rows, problems, no_reads = [], [], []
    # Every attempt's .dfy is kept under attempts/ once the brief says so.
    # Enforced only for campaigns whose brief carries the rule: campaigns 1-8
    # predate it and deleted their failed attempts.
    import glob as _glob
    keeps_attempts = any("/attempts/<pid>/<sid>.<n>.dfy" in open(f).read()
                         for f in _glob.glob(os.path.join(args.batch, "PROMPT_*.md")))
    for sid, m in sorted(manifest.items()):
        t = traj.get(sid)
        p = proofs.get(sid)
        claimed = (t or {}).get("outcome")
        verified = bool(p and p.get("verified"))
        rec = {
            "solution_id": sid,
            "label": m["label"],
            "claimed": claimed or "not attempted",
            "verified": verified,
            "proved_bound": (p or {}).get("proved_bound"),
            "relation": (t or {}).get("relation"),
            "why_failed": (t or {}).get("why_failed"),
            "obstacle": (t or {}).get("obstacle"),
            "attempts_used": (t or {}).get("attempts_used"),
            "seconds": (t or {}).get("seconds"),
            "slice": (t or {}).get("_slice"),
            "reads": (t or {}).get("reads"),
            # a row revised after the campaign keeps what the agent achieved
            "agent_outcome": (t or {}).get("agent_outcome", claimed or "not attempted"),
            "revised": bool((t or {}).get("revision")),
        }
        rerun = (t or {}).get("rerun")
        if rerun:
            rv = rerun_verify.get(sid, {})
            rec["rerun"] = True
            rec["rerun_proof"] = rerun.get("proof")
            rec["rerun_proof_verified"] = rv.get("verified") if claimed == "proved" else None
        rows.append(rec)
        if t is None:
            problems.append(f"{sid}: no trajectory entry")
        elif rerun:
            rv = rerun_verify.get(sid, {})
            # a rerun proof promoted into the overlay is judged there, like any
            # other proof
            if str(rerun.get("proof") or "").startswith("solutions-proved/"):
                rv = {"verified": verified, "assume_count": (p or {}).get("assume_count", 0)}
                rec["rerun_proof_verified"] = verified if claimed == "proved" else None
            if rerun.get("not_promoted"):
                not_promoted.append(sid)
            if claimed == "proved" and not rv.get("verified"):
                problems.append(f"{sid}: rerun claims proved, its own proof does not verify")
            if rv.get("assume_count"):
                problems.append(f"{sid}: rerun proof carries {rv['assume_count']} assume(s)")
            if claimed != "proved" and verified:
                not_used.append(sid)
        elif claimed == "proved" and not verified:
            problems.append(f"{sid}: claimed proved, verifier disagrees")
        elif claimed == "unresolved" and verified:
            problems.append(f"{sid}: claimed unresolved, but a verified proof exists")
        if t and t.get("relation") not in RELATIONS:
            problems.append(f"{sid}: relation {t.get('relation')!r} not in vocabulary")
        # every unresolved record names its obstacle, from the vocabulary
        if t and t.get("outcome") != "proved" and t.get("obstacle") not in OBSTACLES:
            problems.append(f"{sid}: unresolved with obstacle {t.get('obstacle')!r}"
                            " -- set a code from the vocabulary")
        if t and t.get("relation") == "contradicts" and not t.get("relation_reason"):
            problems.append(f"{sid}: contradicts with no reason given")
        if p and p.get("assume_count"):
            problems.append(f"{sid}: proof carries {p['assume_count']} assume(s)")
        if keeps_attempts and t is not None:
            pid = sid.split("_")[0]
            kept = _glob.glob(os.path.join(args.batch, "attempts", pid, f"{sid}.*.dfy"))
            if not kept:
                problems.append(f"{sid}: no attempt kept under attempts/{pid}/ -- "
                                "every attempt's .dfy must be saved")
            elif len(kept) < (t.get("attempts_used") or 0):
                problems.append(f"{sid}: {t.get('attempts_used')} attempts recorded, "
                                f"{len(kept)} kept under attempts/{pid}/")
        # The reading trace. Reported, never repaired: a `reads` array is a
        # record of what an agent actually opened, so a missing one can only
        # be counted, not filled in afterwards.
        if t is not None and not t.get("reads"):
            no_reads.append(sid)

    # A proof must be a proof of the row as written. Output-equivalence is not
    # enough: campaign 7's rerun had four verified proofs that added non-ghost
    # counters or restructured an append. Ghost code is erased on compilation,
    # so the row and an annotation-only proof emit identical Python.
    jobs = {}
    for sid, m in manifest.items():
        found = glob.glob(os.path.join(args.repo, "solutions-proved", "**",
                                       f"{sid}.dfy"), recursive=True)
        rp = ((traj.get(sid) or {}).get("rerun") or {}).get("proof")
        if not found and rp and os.path.exists(os.path.join(args.repo, rp)):
            found = [os.path.join(args.repo, rp)]
        if found:
            jobs[sid] = sorted(found)[0]
    with ThreadPoolExecutor(max_workers=os.cpu_count() or 2) as ex:
        ident = dict(zip(jobs, ex.map(
            lambda sid: identity(args.repo, sid, manifest[sid], jobs[sid]), jobs)))
    for rec in rows:
        sid = rec["solution_id"]
        rec["emitted_python"] = ident.get(sid)
        if ident.get(sid) == "differs":
            problems.append(f"{sid}: {os.path.relpath(jobs[sid], args.repo)} changes "
                            "the row's executable code (emitted Python differs)")
        elif sid in ident and ident[sid] != "identical":
            problems.append(f"{sid}: emitted-Python check {ident[sid]}")
        # A proof must not narrow the row's contract: a needed precondition
        # goes into the row, through its gates, and is then copied over.
        changed = (contract_changes(args.repo, sid, manifest[sid], jobs[sid])
                   if sid in jobs else [])
        rec["requires_changed"] = changed
        if changed:
            problems.append(f"{sid}: proof changes `requires` of "
                            + ", ".join(changed) + " -- fix the row, not the proof")

    # A trajectory that cannot be read line by line is not a missing result.
    for name in sorted(os.listdir(args.batch)):
        if name.startswith("traj_") and name.endswith(".jsonl"):
            problems.extend(jsonl_problems(os.path.join(args.batch, name)))

    # An agent deleting a proof that is not its own. prove-sample-5's slice C
    # removed solutions-proved/2914/2914_264.dfy -- a verified proof for a
    # DIFFERENT solution of the problem it was working on -- while cleaning up
    # its own failed 2914_3. Only `git status` caught it.
    deleted = subprocess.run(
        ["git", "diff", "--name-only", "--diff-filter=D", "HEAD",
         "--", "bigodafny/solutions-proved"],
        cwd=os.path.join(args.repo, ".."), capture_output=True, text=True,
    ).stdout.split()
    for path in deleted:
        sid = os.path.basename(path)[:-4]
        if sid not in manifest:
            problems.append(f"{path}: proof deleted, and {sid} is not in this batch")

    # A row drawn although it already had a proof. The sampler missed
    # solutions-proved/value-bounded/ for one campaign and 12 rows rejoined the
    # pool; two were redrawn and one agent spent its budget rediscovering that.
    for sid in manifest:
        found = [p for p in glob.glob(
            os.path.join(args.repo, "solutions-proved", "**", f"{sid}.dfy"),
            recursive=True)]
        if len(found) > 1:
            problems.append(f"{sid}: {len(found)} proof files -- " + ", ".join(found))

    # The originals are the control. An agent that edited solutions/ to make a
    # proof close has proved nothing.
    dirty = subprocess.run(
        ["git", "status", "--porcelain", "--", "bigodafny/solutions"],
        cwd=os.path.join(args.repo, ".."),
        capture_output=True,
        text=True,
    ).stdout.strip()
    if dirty:
        problems.append("solutions/ is modified:\n" + dirty)

    proved = [r for r in rows if r["verified"]]
    summary = {
        "batch": args.batch,
        "drawn": len(manifest),
        "proved": len(proved),
        "unresolved": len(rows) - len(proved),
        "by_label": {},
        "by_relation": {},
        "obstacles": {},
        "problems": problems,
        # `proved` above is the verifier's view of the rows as they stand now.
        # A row proved by hand after the campaign counts there, not here: this
        # block is what the campaign's bounded agents achieved.
        "campaign": {
            "proved": sum(1 for r in rows if r["agent_outcome"] == "proved"),
            "unresolved": sum(1 for r in rows if r["agent_outcome"] != "proved"),
            "revised_after": sorted(r["solution_id"] for r in rows if r["revised"]),
        },
        "rerun": {
            "rows": sum(1 for r in rows if r.get("rerun")),
            "proved": sum(1 for r in rows if r.get("rerun") and r["claimed"] == "proved"),
            "unresolved": sum(1 for r in rows if r.get("rerun") and r["claimed"] != "proved"),
            "existing_proof_not_used": sorted(not_used),
            "not_promoted": sorted(not_promoted),
        },
        "emitted_python": {
            "checked": len(ident),
            "identical": sum(1 for v in ident.values() if v == "identical"),
            "differs": sorted(s for s, v in ident.items() if v == "differs"),
            "error": sorted(s for s, v in ident.items()
                            if v not in ("identical", "differs")),
        },
        "requires_changed": sorted(r["solution_id"] for r in rows
                                   if r.get("requires_changed")),
        "reads_missing": sorted(no_reads),
        "reads_coverage": (
            round(1 - len(no_reads) / len(rows), 4) if rows else None),
    }
    for r in rows:
        lab = summary["by_label"].setdefault(r["label"], {"drawn": 0, "proved": 0,
                                                          "campaign_proved": 0})
        lab["drawn"] += 1
        lab["proved"] += 1 if r["verified"] else 0
        lab["campaign_proved"] += 1 if r["agent_outcome"] == "proved" else 0
        if r["verified"]:
            key = r["relation"] or "unrecorded"
            summary["by_relation"][key] = summary["by_relation"].get(key, 0) + 1
        elif r["obstacle"]:
            summary["obstacles"][r["obstacle"]] = (
                summary["obstacles"].get(r["obstacle"], 0) + 1
            )

    with open(f"{args.batch}/audit.jsonl", "w") as fh:
        for r in rows:
            fh.write(json.dumps(r) + "\n")
    with open(f"{args.batch}/summary.json", "w") as fh:
        json.dump(summary, fh, indent=2, sort_keys=True)

    print(json.dumps({k: v for k, v in summary.items()
                      if k not in ("problems", "reads_missing")}, indent=2))
    if no_reads:
        print(f"\n{len(no_reads)} row(s) carry no reading trace: "
              + " ".join(sorted(no_reads)), file=sys.stderr)
    if problems:
        print("\nPROBLEMS", file=sys.stderr)
        for p in problems:
            print("  " + p, file=sys.stderr)
        return 1
    print("\nno disagreement between trajectories and the verifier")
    return 0


if __name__ == "__main__":
    sys.exit(main())
