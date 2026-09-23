# What changed between campaigns, and what that costs the pooled numbers

Seven campaigns have run. **They were not run under one configuration.** The
brief, the charge table, the sampler and the recorded schema all moved between
them, so a number pooled across all seven is pooled across several
measurements. This file is the map: what differed, when, and which numbers it
touches.

Every row below is read off the files in this directory and the git history,
not from recollection.

| campaign | drawn | date |
|---|---|---|
| `prove-sample` | 50 | 2026-09-16 |
| `prove-sample-2` | 50 | 2026-09-21 |
| `prove-sample-3` | 50 | 2026-09-21 |
| `prove-sample-4` | 50 | 2026-09-21 |
| `prove-sample-5` | 50 | 2026-09-22 |
| `prove-sample-6` | 50 | 2026-09-23 |
| `prove-sample-7` | 50 | 2026-09-23 |

Campaign 7 is the first drawn with `--exclude-drawn` and the first to collect
a reading trace, though only for the 20 rows whose slices ran after that
requirement was added mid-campaign.

## What each campaign's brief said

Checked by grepping each batch's own `PROMPT*.md` — the brief the agents
actually ran under, not the current skill template.

| in the brief | c1 | c2 | c3 | c4 | c5 | c6 | c7 |
|---|---|---|---|---|---|---|---|
| `s[i := v]` charged 1, not `\|s\|` | ✔ | ✔ | ✔ | ✔ | ✔ | ✔ | ✔ |
| value-versus-size convention | — | ✔ | ✔ | ✔ | ✔ | ✔ | ✔ |
| `tighter-translation` / `tighter-costmodel` relations | — | — | ✔ | ✔ | ✔ | ✔ | ✔ |
| `IntToString(x)` and `\|IntToString(x)\|` charge 1 | — | — | — | — | — | ✔ | ✔ |
| `reads` trace required | — | — | — | — | — | — | 20/50 |

The seq-update charge is the one thing uniform across all seven. Everything
else splits the series.

## What that means for each number

**The pass rate** is comparable across c1–c6 as far as the charge table goes,
with one exception: `IntToString` became free in c6. A row whose cost is
dominated by digit strings was harder in c1–c5 than in c6–c7, and nobody has
counted how many such rows there are.

**The relation vocabulary widened, and the recorded files do not all reflect
it.** c1's and c2's briefs offered four values; `tighter-costmodel` and
`tighter-translation` were added for c3. What each batch's
`label_relation.jsonl` holds is the orchestrator's hand-normalisation, not the
agent's raw claim, so c2's file does carry both new values — it was normalised
after they existed. c1's was not: its file records `unresolved` as a relation
for 8 rows, which is not in the vocabulary at all, and only 17 of its 50 rows
appear in the file. Pooling relations across all seven is pooling one
un-normalised campaign with six normalised ones.

**The draw changed twice.**

- c5's pool wrongly included 12 already-proved rows, through a sampler bug
  (`sample.py` listed the overlay flat and missed `value-bounded/`). Two were
  redrawn. `provestats.py` excludes them by id.
- c1–c6 drew plainly, so each carries more rows an earlier campaign already
  failed: 0%, 4%, 10%, 12%, 24%, 28%. c7 uses `--exclude-drawn`.
  `data/prove_stats.md` § *Fresh rows versus redrawn rows* splits every
  campaign both ways; that table, not the headline, is the comparable one.

**The recorded bounds moved without any proof changing.** `proofs.py`'s
`bound_of` was rewritten on 2026-09-22: before it, 3 proofs recorded no bound
and 7 recorded a helper's rather than `Solve`'s. Bounds read out of a snapshot
taken before that date are not the bounds in the files.

**c7 is itself mixed.** A session rate limit killed all three slice agents
part-way. Slice B (17 rows) and slice C's first 13 finished before the `reads`
requirement existed and have no trace; slice A and the 3 remaining C rows were
re-run under it. Slice A's 14 proofs from the killed run had no trajectory
behind them and were discarded rather than kept, so the re-run measures a real
budget. `reads_coverage` is **0.4** for c7 and 0 before it.

## The 2026-09-23 revision: records brought to the latest version

The prelude gained a composable sort-cost bound (`SortCost`, opaque `NLogN`,
`SortCostNLogN`, `SortCostWithin`) and a binary-search potential
(`SearchPot`, `BisectStep`, `SearchLoopWithin`). With them, by hand and
outside every campaign's budget, 30 rows' campaign records changed
(two more, `1484_82` and `603_284`, predate the campaigns and have none):

- 19 proved rows went from `looser-slack` to `confirms` — the quadratic
  `SortCost` scaffold, or `85_71`'s linear-scan binary-search bound, replaced
  by the tight one;
- `2128_34` kept `looser-structural` but lost its quadratic sort term: its
  label's n**2 is the DP's |neg| x r, a value term the proof already carried,
  not the sorts as an earlier note said;
- 10 unresolved rows were proved: `2105_248`, `661_47`, `1039_15`, `2826_81`,
  `2128_3`, `1387_19`, `1892_121`, `1582_118`, `1827_66` confirm their
  labels, and `1718_1166` is `looser-structural`.

**How the files hold it.** The current files carry each row's latest state.
Every superseded line — trajectory, relation, obstacle, audit — is in that
batch's `old_record.jsonl` as `{"file", "superseded_on", "why", "record"}`.
Each revised trajectory keeps `agent_outcome`, `agent_relation` and
`agent_bound` beside the current values, plus a `revision` block naming who
produced the current state.

**The same pass brought older records current.** Re-running every batch's
audit against the new proofs showed 20 more stale lines: rows an early
campaign failed and a later one proved (16 rows, e.g. `1972_295`, failed in
c2 and proved in c6) and `2423_48`, proved by hand on 2026-09-22. Those were
revised the same way, their `revision.by` naming the proving campaign or
`hand`. Two lines were deliberately left: `2128_34` and `2942_42` in campaign 1,
whose own `traj_convention.jsonl` records the proof from that campaign's
convention re-run.

In all 47 rows were revised and 149 superseded lines kept. All six audits
(c2–c7) report no disagreement between trajectories and the verifier.

**What it does not change.** Every campaign rate. `provestats.py`,
`collect.py`, `dedupe.py` and `audit.py` compute campaign tables from
`agent_outcome`, so a row a bounded agent missed stays missed in its campaign;
the campaign-era tables in `data/prove_stats.md` are unchanged, and each
campaign's count in `data/artifact_data.json` matches its history. The current
state is reported beside them: 272 of 311 distinct drawn rows carry a proof
now, 261 proved by a bounded agent, 11 closed afterwards by hand.

It also settles one of the questions below by construction: pooled relation
tables now describe proofs of one standard. No proof's bound uses a quadratic
sort scaffold or charges a sort linearly; the only files still defining the
old quadratic lemma are the two duplicates under `solutions-proved/nlogn/`,
where it is unused beside their tight bound.

## What a cleanup would have to decide

Open, not settled here:

1. Whether to re-derive c1 and c2's relations under the 6-value vocabulary by
   re-reading their proved bounds against their labels. That is re-judging
   recorded data, not re-running it, and is defensible — but it must be
   written as a separate normalisation pass with its own file, never edited
   into the original trajectories.
2. Whether the pooled rate should be quoted over fresh rows only. The
   fresh/repeat split exists per campaign; the headline currently does not use
   it. **Partly settled:** `dedupe.py` now reduces the record to one entry per
   distinct row, keeping the most positive outcome, so the campaigns
   partition. 300 draw records become 261 rows, and the rate over them is
   221/261 = 85% against the raw 221/298 = 74% — the same proofs, a
   denominator with the duplicate draws taken out. Use it for the corpus;
   per-campaign comparison still belongs to the raw records, because
   attributing a row to whichever campaign proved it flatters the later one.
3. Whether `IntToString`-dominated rows in c1–c5 should be identified and
   marked, so the c6 change is visible rather than silent.
4. What to do with the c7 rows that carry no `reads`. They cannot be
   backfilled — a trace is a record of what an agent opened. Either c7 reports
   partial coverage, or B and C are re-run, which is itself invalid while
   their proofs sit in `solutions-proved/`.

None of these may be resolved by editing a trajectory file. A trajectory is
what an agent recorded; a later judgement about it goes in its own file beside
it, as `label_relation.jsonl` already does.
