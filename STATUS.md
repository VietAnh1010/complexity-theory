# Status

Live run state. **Update after every batch, then commit.** If the session
dies, this file plus the git log is the entire handoff.

---

## Current

- **Phase:** not started — repo scaffolded, pipeline smoke-tested end to end
- **Last updated:** 2026-08-10
- **Next action:** Phase 1 harvest, per `prompts/mine-dataset.md`
- **Library state:** holds the 76-record smoke test, not a real run.
  - Reset it before the real harvest, or keep it and let dedup absorb it.

## Counts

| | |
|---|---|
| records | 76 |
| candidates | 72 |
| included | 4 |
| excluded | 0 |
| unavailable | 0 |
| with an abstract | 60 |
| with a DOI | 55 |

_Refresh with `python3 scripts/dataset.py` and read `dataset/stats.json`._

## Coverage by subarea

From the smoke test, not a real harvest. Every number here is expected to move.

| Subarea | Records |
|---|---|
| circuit-complexity | 61 |
| meta-complexity | 20 |
| derandomization | 15 |
| quantum-complexity | 12 |
| structural | 8 |
| algebraic-complexity | 6 |
| communication-complexity | 6 |
| hardness-of-approximation | 5 |
| proof-complexity | 5 |
| interactive-proofs | 5 |
| query-complexity | 5 |
| average-case | 4 |
| space-complexity | 4 |
| fine-grained | 3 |
| counting-complexity | 2 |
| parameterized | 1 |
| total-search | 1 |
| descriptive-logic | 0 |

The skew is an artifact of the two smoke-test queries, both about circuit lower
bounds. It is not a finding.

## Snowball rounds

| Round | Direction | Seeds | Seeds w/o DOI | New records |
|---|---|---|---|---|
| smoke | both | 4 | 0 | 39 |

Reach, from what `snowball.py` printed:

- backward: 92 unseen references across 4 seeds; 65 references had no DOI.
- forward: 2 of 4 seeds had citing works in OpenCitations; 2 had none.

Stopping criterion (`SCOPE.md`): two consecutive rounds each yielding fewer
than 25 new in-scope records.

## Citation graph

From `scripts/dataset.py --edges` on the smoke-test library:

| | |
|---|---|
| edges | 116 |
| papers queried | 54 |
| papers without a DOI | 21 |
| references seen | 2211 |
| references deposited unstructured | 592 |
| references pointing outside the library | 1502 |

592 of 2211 references were deposited as plain text, so 27% of the citation
graph is invisible to Crossref. Report that number, not just the edge count.

## Open questions

Things to raise with the user rather than block on. Record and keep going.

- No seed papers supplied. The harvest runs on `config/queries.txt` alone.
  - Seeds would improve Phase 3 reach.
  - Resolve any through `search_arxiv.py --query "<title>"`.
  - Never enter one by hand into the library.
- `descriptive-logic` matched nothing in the smoke test. Untested regex.

## Decisions made under uncertainty

Judgement calls worth a second look. Borderline include/exclude calls, subarea
assignments, records cut for balance.

| Record | Call | Why |
|---|---|---|
| — | — | — |

## Run log

Append one line per batch: what ran, what it yielded.

- `2026-08-10` — repo ported from `lightweight-survey`; subject retargeted.
  - Pipeline verified end to end against live arXiv, Crossref, OpenCitations.
  - Citation gate catches a planted non-existent DOI and a planted title
    mismatch; exits 1 on both.
  - Four metadata bugs found and fixed, all of which hit old records hardest.
    - Crossref deposits inline markup inside titles; it broke dedup.
    - Old ACM proceedings deposit an `event.name` naming no committee.
    - ECCC matched the `CC` journal pattern and was tagged target tier.
    - Venues matching nothing were never retried after the table improved.
  - No year floor: backward snowball from 4 seeds reached 10 pre-2000 papers.
    - Among them Natural Proofs (1994) and Impagliazzo-Wigderson (1997).
