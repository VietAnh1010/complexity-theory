# Status

Live run state. **Update after every batch, then commit.** This file plus the
git log is the entire handoff.

## Current

- **Phase:** harvest complete (107 queries, 0 failures); 2471 records
- **Last updated:** 2026-08-10
- **Next action:** `run.py enrich`, then screen the core tier

Coverage targets in `SCOPE.md` all met: every subarea over 50, largest at 20%,
0 uncategorized, 2455 of 2471 with an abstract. Only 469 carry a DOI, so
snowballing reaches under a fifth of the library until `enrich` runs.

## Counts

_Refresh with `run.py dataset`, then read `dataset/stats.json`._

## Snowball rounds

| Round | Direction | Seeds | Seeds w/o DOI | New |
|---|---|---|---|---|
| smoke | both | 4 | 0 | 39 |

Smoke round reach: 92 unseen refs across 4 seeds, 65 refs with no DOI; 2 of 4
seeds had citing works in OpenCitations.

Stopping criterion (`SCOPE.md`): two consecutive rounds each under 25 new.

## Citation graph

From `run.py dataset --edges` on the 76-record smoke library:

| | |
|---|---|
| edges | 116 |
| papers queried | 54 |
| papers without a DOI | 21 |
| references seen | 2211 |
| deposited unstructured | 592 |
| pointing outside the library | 1502 |

592 of 2211 refs were plain text, so 27% of the graph is invisible to Crossref.
Report that alongside the edge count.

## bigodafny — Python → Dafny dataset

Separate deliverable in `bigodafny/`, built from BigOBench's
`time_complexity_test_set`. Shares nothing with the paper pipeline.

- **Phase:** pipeline complete and proven end-to-end; translations not started
- **Last updated:** 2026-08-31
- **Next action:** choose a translator — see Open questions

| | |
|---|---|
| rows / problems | 640 / 311 |
| split `strict` / `loose` | 540 / 100 |
| signatures synthesized | 636 of 640 rows (309 of 311 problems) |
| Dafny translations valid | 5 (hand-written) |
| Dafny / Z3 | 4.11.0 / 4.12.1 |

**The split is measured, not read.** Running the original Python against its own
stored tests, only 540 of 640 reproduce the expected output byte-for-byte.
Codeforces accepted the rest under token-based or special checkers, so the
stored output is one accepted answer. 540 is the ceiling for any translation.

The description regex I first planned to split on scores precision 0.38, recall
0.45 against that measurement. It is kept as `nondet_hint` and gates nothing.

**Two problems have no synthesizable signature** (4 rows): `1042_A. Benches` and
`490_A. Team Olympiad` annotate a field as bare `list` with no element type.
Recorded, not guessed.

**Scale check:** 120 rows validated, 4,054 tests executed, 9 distinct Dafny
parameter types including `seq<seq<real>>` and `seq<(string, string)>`. Zero
build failures, zero marshalling errors. The 118 non-hand-written rows failed on
output, which is what an untranslated stub should do.

**Proven end-to-end:** 5 hand-written translations spanning scalar, `seq<int>`,
`string`, `seq<seq<int>>` and `seq<(int,int)>` pass 545/545 tests across all
three tiers. `cli.py selftest` asserts a wrong answer reports as `fail` and a
syntax error as `build`; it already caught a fixture bug that made every case
look like a build failure.

`prelude.dfy` verifies clean and is cross-checked against CPython: `FloorDiv`
and `FloorMod` agree with Python `//` and `%` on 1458/1458 cases. Dafny's own
`/` is Euclidean and disagrees whenever the divisor is negative.

Licence carries over: BigOBench is **CC-BY-NC-4.0**, so the derived dataset is
non-commercial. See `bigodafny/LICENSE.md`.

## Open questions

- No seed papers supplied; the harvest runs on `config/queries.txt` alone.
  - Resolve any through `run.py harvest --query "<title>"`.
  - Never enter one by hand into the library.
- Eight queries were dead or near-dead; rewritten and re-run, worth 162 records.
  - arXiv matches each concept as a literal phrase.
  - Three-concept ANDs and LaTeX-written class names return nothing.
- `bigodafny`: no translator chosen. The validator will judge any candidate.
  - An LLM behind the validator is the only route that covers 636 varied rows.
  - `CLAUDE.md`'s "no model in this pipeline" was written for the paper
    pipeline; `bigodafny/CLAUDE.md` scopes it to the deterministic stages.
  - A rule-based transpiler must cover: string ops 487 rows, sort-with-key 151,
    `//` 131, dict/Counter 55, set 52.
- `bigodafny`: whether to widen past `time_complexity_test_set`.
  - The 311 problems hold 249,912 human solutions upstream; the test set keeps 640.

## Decisions made under uncertainty

| Record | Call | Why |
|---|---|---|
| — | — | — |

## Run log

- `2026-08-10` — ported from `lightweight-survey`; subject retargeted, no LLM
  content anywhere.
  - Verified end to end against live arXiv, Crossref, OpenCitations.
  - Gate catches a planted fake DOI and a planted title mismatch; exits 1.
  - Four metadata bugs found and fixed, all worst on old records.
    - Crossref deposits inline markup in titles; it broke dedup.
    - Old ACM proceedings deposit an `event.name` naming no committee.
    - ECCC matched the `CC` pattern and was tagged target tier.
    - Venues matching nothing were never retried after the table improved.
  - No year floor: backward snowball from 4 seeds reached 10 pre-2000 papers.
    - Among them Natural Proofs (1994) and Impagliazzo-Wigderson (1997).
- `2026-08-10` — first full harvest hit arXiv 429s after ~30 queries at the
  documented 3s floor.
  - Fixed by `ARXIV_RATE_SECONDS`; a full grid at 10s completes clean.
  - Harvest now saves every 5 queries; it previously saved only at the end.
    - The first attempt was killed and lost all 33 completed queries.
- `2026-08-10` — repo golfed: 13 scripts to 4 modules and one CLI.
  - `lib.py`, `topic.py`, `sources.py`, `run.py`; `prompts/` folded into CLAUDE.md.
  - Traps that were comments are now a README section, so they survive edits.
- `2026-08-10` — full harvest: 107 queries at 10s spacing, 0 failures, 2471 records.
  - Five queries returned 0 hits and mapped onto the two thin subareas.
    - `total-search` and `descriptive-logic` were a grid artifact, not a thin
      literature. Rewriting the queries closed both gaps.
