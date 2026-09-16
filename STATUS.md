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

- **Phase:** translated and gated; label audit complete; cost model axiomatised
- **Last updated:** 2026-09-16
- **Next action:** review the 178 disputed rows; screen the 127 unscreened ones

| | |
|---|---|
| rows / problems | 640 / 311 |
| split `strict` / `loose` / unvalidatable | 534 / 100 / 6 |
| translated | 636 of 640 (4 cannot be — bare `print(float)`) |
| behaviour gated | 529 valid, 3 fail |
| safety verified | 350 of 636 |
| complexity proved | 31 rows, 33 files, all verify, zero `assume` |
| label audit | 506 screened: 321 `ok`, 178 `mismatch`, 7 `unsure` |
| Dafny / Z3 | 4.11.0 / 4.12.1 |

**Rows are partitioned by status**, one directory each, each with a `README.md`:
`solutions/` 328, `solutions-unscreened/` 127, `solutions-disputed/` 178,
`solutions-unverified/` 3, `solutions-untranslated/` 4. `solutions-proved/` is
an overlay of instrumented copies, not a sixth bucket.

**The split is measured, not read.** Running the original Python against its own
stored tests, only 540 of 640 reproduce the expected output byte-for-byte.
Codeforces accepted the rest under token-based or special checkers, so the
stored output is one accepted answer. `difftest.py` gates those against their
own Python instead. The description regex first planned for the split scores
precision 0.38, recall 0.45 against the measurement; it survives as
`nondet_hint` and gates nothing.

**The cost model is a stipulated axiom set, not a measurement.** `s[i := v]`,
`m[k := v]` and set insertion are charged O(1) regardless of backend
(`bigodafny/COMPLEXITY.md`, `batches/cost-axioms/PLAN.md`). The measured
alternative made a row's class depend on which backend compiled it, and the
labels were measured on CPython, so it compared two unrelated implementations.
Consequence: `validate.py` and `difftest.py` check behaviour only, and the
complexity claim is checked by proof in `solutions-proved/`. That is intended —
a label that moves with the runtime is a benchmark result, not a label.

`array<T>` has been removed from the corpus for the same reason; two rows keep
one because their tables are too large for the backend to copy per update, and
each says so in a header comment.

**Two problems have no synthesizable signature** (4 rows): `1042_A. Benches` and
`490_A. Team Olympiad` annotate a field as bare `list` with no element type.
Recorded, not guessed.

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
- `bigodafny`: **resolved** — agents translated all 636 rows behind the
  validator. `CLAUDE.md`'s "no model in this pipeline" was written for the paper
  pipeline; `bigodafny/CLAUDE.md` scopes it to the deterministic stages.
- `bigodafny`: 178 rows sit in `solutions-disputed/` awaiting manual review.
  - 112 need the **label** changed, 58 the **translation**, 7 both, 1 neither.
  - Re-filing under the cost axioms should return 30-40 of the 58 to `solutions/`;
    that step (`batches/cost-axioms/PLAN.md` § 3) has not been run, because it
    changes verdicts already queued for review.
  - One convention is unsettled across 11 rows: whether a loop bounded by the
    *value* of a capped scalar counts as constant. See
    `solutions-disputed/README.md`.
- `bigodafny`: 127 rows in `solutions-unscreened/` have never been through the
  label audit at all.
  - They were quarantined earlier for sibling convergence (12) or for using
    `set<T>`/`map` (29), and the second reason no longer justifies anything
    under the axioms.
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
