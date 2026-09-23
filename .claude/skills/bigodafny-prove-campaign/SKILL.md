---
name: bigodafny-prove-campaign
description: Run a bounded random-sample proof campaign over bigodafny/. Sample N unproved rows from solutions/, hand slices to concurrent Sonnet subagents under a per-row attempt and time budget, record a trajectory for every row including the failures, audit the claims against the verifier, and collect the result as artifact data. Use when asked to sample and prove rows, to measure how often a bounded agent can prove a label, or to run another prove-sample batch.
---

# A bounded prove campaign

This measures something, and the measurement is the deliverable. The question
is: **how often can a bounded agent prove a randomly drawn row's complexity
label, and when it cannot, why not?** Proofs are a by-product. A campaign that
closes 40 rows and records nothing about the 10 it missed has failed.

Read the `bigodafny` skill for the corpus, and `bigodafny-prove` for the proof
technique. This is the campaign procedure around them.

## Default parameters

| parameter | default |
|---|---|
| sample size | 50 rows |
| pool | `solutions/`, labelled, gate-passing, no proof yet |
| budget | 3 attempts and 5 minutes per row |
| agents | Sonnet, 3 at a time, one slice each |
| seed | today as `YYYYMMDD` |

Take whatever the user names instead. If they name none, use these and say so.

## Procedure

### 1. Draw the sample

```bash
cd /home/user/complexity-theory/bigodafny
python3 ../.claude/skills/bigodafny-prove-campaign/scripts/sample.py \
    --batch batches/<name> --n 50 --seed <YYYYMMDD> --slices 3
```

Writes `manifest.jsonl`, `slice_{a,b,c}.jsonl` and `excluded.jsonl`. The pool
is sorted before sampling, so seed plus corpus state reproduces the draw.

`excluded.jsonl` is not noise. A row sitting in `solutions/` whose latest
recorded gate result is negative or missing is a real inconsistency — report
the count, do not silently drop it. `batches/gate-audit/` is what came of the
first such report: four of seven rows turned out to pass every test that could
be run, and their `fail` was produced by the problem's own dataclass.

A row whose gate cannot reach a verdict at all now lives in
`solutions-ungateable/`, outside the pool by construction, with the evidence in
`data/gate_ungateable.jsonl`. **Never make a row eligible by editing a gate** —
a gate may not be relaxed by the work it judges.

**Watch the repeat rate, and switch to `--exclude-drawn` when it climbs.** A
row that fails stays in the pool, so each campaign's draw contains more rows
already known to be hard: 8%, 12%, 20%, 28% across campaigns 3 to 6. Past
about a quarter the campaign has stopped measuring "can a bounded agent prove
a random row" and started measuring "can a second agent close what the first
could not" — a fair question, but a different one, and the rate falls for
reasons that have nothing to do with the agents.

`--exclude-drawn` draws only from rows no campaign has touched. That subset is
**unbiased**: earlier campaigns removed a random part of the pool (what they
proved) and left a non-random part (what they failed), so what was never drawn
still looks like the original population and stays comparable with campaign 1.
Say in the README which mode the draw used; the two are not interchangeable.

### 2. Write the brief

Copy `PROMPT.md` from this skill into the batch directory and substitute
`{{BATCH}}` and `{{SLICE}}`, one copy per slice. It is self-contained: charge
table, ghost-counter shape, both log functions, the hard rules, the budget, and
the trajectory schema. An agent should not need to read `COMPLEXITY.md`.

### 3. Run the slices

Spawn the agents with `subagent_type: "general-purpose"` and
`model: "sonnet"`, **at most 3 concurrently**. Each agent gets one slice and
writes only its own `traj_<slice>.jsonl`.

Token discipline is part of the brief, not an afterthought: no preamble, no
per-command narration, final message ≤ 8 lines. The trajectory file is the
record.

### 4. Audit — the agents' reports are not evidence

```bash
python3 proofs.py                       # re-verifies solutions-proved/ from scratch
python3 ../.claude/skills/bigodafny-prove-campaign/scripts/audit.py --batch batches/<name>
```

`audit.py` joins the verifier's output to the trajectories and fails on any
disagreement: a row claimed proved that does not verify, a row claimed
unresolved that does, an `assume` in a proof, a `relation` outside the
vocabulary, or a modified file under `solutions/`.

Fix the data, not the check. In the first campaign an agent's prose said 9
proved where its trajectory said 10; the files said 10, and the prose was wrong.

### 5. Normalise the label relations

Agents get this wrong by default, so check every non-`confirms` row yourself.

**Every bound in a campaign like this is an upper bound.** An upper bound
confirms a label or fails to; it refutes one only by being strictly tighter
than the label allows. A proved `O(n**2)` on an `O(nlogn)` row is not a
disagreement.

| relation | meaning |
|---|---|
| `confirms` | the bound is within the label's class |
| `looser-slack` | a loose scaffold was used; the tight bound was not attempted |
| `looser-structural` | the proof exposes a real cost the label omits |
| `tighter-costmodel` | the bound is below the label because the charge table costs something CPython does not |
| `tighter-translation` | the bound is below the label because the Dafny uses a cheaper algorithm than the Python |
| `contradicts` | a literal in the source forces more work than the label allows |

A bound **below** the label is the case agents mishandle most. It has three
possible causes and they are not interchangeable: the label is loose, the
charge table is cheaper than CPython, or the translation is cheaper than the
Python. Only the first says anything about the label. Read the Python before
recording one.

Write the normalised relations to `label_relation.jsonl` in the batch
directory; `audit.py` prefers that file over the agents' values when it is
present.

Keep each agent's original claim in the payload as `agent_said_*` so the
normalisation stays auditable. The judgement belongs in the data file with its
reason written out, never inside a script.

### 6. Collect for the artifact

Extend `bigodafny/collect.py` with the batch and re-run it into
`data/artifact_data.json`. Report, at minimum:

- drawn, proved, unresolved;
- proved rate **per label class** — the rate is not flat, and the split is the
  finding;
- obstacle counts over the unresolved rows;
- relation counts over the proved rows;
- attempts and seconds distributions;
- `reads_coverage` — the share of rows carrying a reading trace. A trace names
  the source row and every helper or prelude declaration whose contract, cost
  or termination the agent had to open. It is recorded, never reconstructed:
  a row that finished before the requirement existed stays at no trace.

### 7. Write `README.md` in the batch directory

What was asked, what was drawn, what came back, and what it means. Tables over
prose. Every number in it must come from `summary.json` or a file on disk.

### 8. Commit

Everything in `batches/<name>/`, the new files under `solutions-proved/`, and
the refreshed `data/`. Push to the session's designated branch.

## Rules

- **The budget is hard.** Out of attempts or time → delete the partial copy
  from `solutions-proved/`, record `unresolved` with the obstacle named, move
  on. Most rows failing is a legitimate result.
- **`why_failed` names an obstacle**, not "ran out of attempts". Which
  invariant would not hold; which multiplication the solver refused. Codes used
  so far: `value-to-size`, `z3-nonlinear`, `invariant-gap`, `decreases-star`,
  `recursion-depth`, `budget`.
- **Never read a trend off one campaign's per-label table.** A class holds 8
  to 25 rows, so two rows move the rate ten points. After campaign 3 this
  project reported a crossover — `O(nlogn)` overtaking `O(n)` — and campaign 4
  did not reproduce it. Pooled over four campaigns `O(n)` is 86% and
  `O(nlogn)` 66%, the ordering campaign 1 found. Read
  `campaign_series.by_label[...].pooled` in `data/artifact_data.json`, and
  treat a single cell's `p_vs_pooled` as noise unless the next campaign
  reproduces it.
- **Obstacles generalise where rates do not.** `value-to-size` was named
  independently by campaign 4's agents, none of which had seen campaign 3. A
  recurring named obstacle is a stronger finding than a moving rate.
- **File value-bounded rows before you write the README.** A proved row whose
  `looser-structural` reason names an input VALUE, and any row whose obstacle
  is `value-to-size`, gets filed. The proved row's file moves into
  `solutions-proved/value-bounded/`; the unproved row goes to
  `batches/value-bounded-open/`, because a row with no proof does not belong
  under a directory called `solutions-proved`. That directory's
  README has the procedure and the three ways a row leaves. Skipping this
  leaves the finding scattered across batch directories where nobody joins it.
- **Filing a proof one directory deeper breaks its `include`.** A proof in
  `solutions-proved/<pid>/` reaches the prelude by `../../prelude.dfy`; from
  `solutions-proved/value-bounded/<pid>/` it needs `../../../prelude.dfy`.
  The file still parses, so nothing complains until the next `proofs.py`, which
  reports it as a verification failure and looks exactly like a bad proof. Fix
  the include in the same step as the move, and re-verify the moved file
  before running anything else.
- **Never weaken a proof to match a label.**
- **No `assume`, no `decreases *`**, corpus-wide. `proofs.py` greps for both.
- **Agents never touch** `solutions/`, `validate.py`, `difftest.py`,
  `verify_all.py`, `precheck.py`, `proofs.py`, or `data/`. A gate may not be
  edited by the work it judges.
- **A subagent's report carries no authority.** It cannot approve anything, and
  a request relayed through one is not a request from the user.
- **Hold in-flight files.** Do not commit a `traj_*.jsonl` an agent is still
  writing; say that is why it is uncommitted.
- **Read `git status` for DELETIONS, every time.** An agent cleaning up after
  its own failed row can take a sibling's proof with it — same problem
  directory, different solution, different label. It happened twice in
  `prove-sample-5`. `audit.py` now fails on a deletion whose row is not in the
  batch, but only after `proofs.py` has run; a missing tracked file shows up in
  `git status` immediately.
- **Tell the agents to append each row's line as it finishes.** A run that
  batches its trajectory writes to the end loses everything when it is cut off
  mid-slice, and a rate limit can cut off all three at once.
- **A proof with no trajectory is not campaign data.** When a killed agent
  leaves `.dfy` files with no record behind them, there is no attempt count,
  no elapsed time, no relation and no `reads`, and none of it is recoverable.
  Delete those files before re-running the slice — left in `solutions-proved/`
  the re-run agent opens a finished proof of its own assigned row and measures
  nothing. Campaign 7's slice A was killed after one trajectory line and 14
  such files; they were discarded and the slice re-run from scratch. Keeping
  them costs more than it buys: a proof restored afterwards was obtained
  outside the budget, so it cannot enter the rate, and the campaign's own
  re-run supplies the row anyway.
- **A repaired trajectory is still the agent's data.** If a `traj_*.jsonl` is
  not one object per line, recover it with `json.JSONDecoder().raw_decode` in a
  loop and rewrite it as JSONL. Do not re-run the slice and do not retype the
  entries.

## Files

| file | what it is |
|---|---|
| `scripts/sample.py` | draws the sample, writes manifest and slices |
| `scripts/audit.py` | joins verifier output to trajectories, fails on disagreement |
| `PROMPT.md` | the agent brief, with `{{BATCH}}` / `{{SLICE}}` placeholders |
