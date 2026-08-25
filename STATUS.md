# Status

Live run state. **Update after every batch, then commit.** This file plus the
git log is the entire handoff.

## Current

- **Phase:** verification tier harvested; enriching, then screening
- **Last updated:** 2026-08-25
- **Next action:** screen `--category verification-complexity`, then snowball

New subarea `verification-complexity`: the machinery under Frama-C, Dafny, Why3,
CBMC. 443 records, all with an abstract, 334 with no DOI. Its admission path is
a cost-of-checking claim, not complexity vocabulary — `SCOPE.md` § In scope.

Screening question for this tier is not "is it in scope" but "has this run on a
large codebase". That verdict is a `tags` value, exported as a column.

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

## Open questions

- Request read as: harvest the literature *behind* Frama-C and Dafny, not run
  those tools on this repo.
  - Nothing here is C or Dafny; there is no program for either to check.
  - The reading that yields work is the theory and cost of program checking,
    filtered for what survives a large codebase. Proceeded on that.
  - If the other reading was meant, the deliverable would be a proof harness,
    not a dataset — say so and it gets built instead.
- No seed papers supplied; the harvest runs on `config/queries.txt` alone.
  - Resolve any through `run.py harvest --query "<title>"`.
  - Never enter one by hand into the library.
- Eight queries were dead or near-dead; rewritten and re-run, worth 162 records.
  - arXiv matches each concept as a literal phrase.
  - Three-concept ANDs and LaTeX-written class names return nothing.

## Decisions made under uncertainty

| Record | Call | Why |
|---|---|---|
| — | — | — |

## Run log

- `2026-08-25` — verification tier added and harvested; library 2471 -> 2909.
  - 54 queries over cs.LO/cs.PL/cs.SE plus the complexity categories, 0 failures.
  - `in_topic` gains one alternative path, for this subarea only.
    - The other 17 keep the original conjunction; no existing record moves.
  - Venue table gains CAV, POPL, PLDI, TACAS, SAS and 18 more.
    - FMCAD had to precede CAV, the same trap as ECCC before CC.
  - 15 queries returned 0-2 hits; rewritten and re-run, worth 48 records.
    - Same failure as the first harvest: three-concept ANDs, invented phrases.
    - `concurrent separation logic` returns 41; the three-concept form returns 0.
  - arXiv reach here is thinner than in complexity: CAV/POPL/PLDI papers often
    never post a preprint. Report as a source gap, not a thin literature.

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
