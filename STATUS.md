# Status

Live run state. **Update after every batch, then commit.** This file plus the
git log is the entire handoff.

## Current

- **Phase:** statement layer built over 501 papers; paper layer unchanged
- **Last updated:** 2026-08-12
- **Next action:** `extract --limit 500` to widen; core tier still at 4 screened
- Paper-layer targets in `SCOPE.md` all met: every subarea over 50, largest 20%,
  0 uncategorized, 2455 of 2471 with an abstract
- Branch `claude/extract-datasets-papers-8zdhcf` is pushed and in sync

## Counts

_Refresh with `run.py dataset` and `run.py examples`; the two stats files hold
the full breakdowns._

| | |
|---|---|
| papers in library | 2471 |
| papers with source extracted | 501 |
| statements | 18641 |
| test items | 3207 |
| distinct classes named | 164 |

- By kind: lemma 4995, theorem 4454, definition 4100, proposition 1377,
  corollary 1360, claim 922, then 7 smaller kinds.
- Every subarea holds ≥1039 statements; largest is `quantum-complexity` at 3116.
- Median 30 statements per paper.

## Statement layer reach

| outcome | papers |
|---|---|
| `ok` | 495 |
| `gone` — arXiv has no source | 3 |
| `pdf-only` | 2 |
| `error` | 1 |
| parsed, no theorem environments | 8 |

- 32 of 2471 library papers have **no arXiv id** and are unreachable here; they
  are the pre-2000 anchors plus journal-only records. Structural, not a bug.
- The 8 zero-yield papers state their results in prose, not in environments.

## Field coverage within statements

| field | statements |
|---|---|
| bounds | 6072 |
| classes | 2651 |
| problems | 2175 |
| measures | 384 |
| hypotheses | 300 |
| problem specifications | 288 |
| relations | 227 |

- 280 relation triples, **168 conditional** — "unless NP ⊆ coNP/poly" is the
  commonest shape.
- Most statements name no class: query, communication and algebraic papers state
  results in measures and bounds.

## Known precision limits

- **One-letter class names are the noisy field.** `E` and `L` are also an edge
  set and a language variable. Guards reject expectations, norms, Euler's number
  and bound variables; some survive. Multi-letter names are reliable.
- **`statement_text` is lossy.** Macros defined in a `.sty` arXiv did not ship
  stay as bare command names. `statement_tex` is exact.
- **The bulk tier is unscreened.** 2467 of 2471 papers are `candidate`, so the
  statement layer includes preprints announcing resolutions of P vs NP.

## Snowball rounds

| Round | Direction | Seeds | Seeds w/o DOI | New |
|---|---|---|---|---|
| smoke | both | 4 | 0 | 39 |

- Reach: 92 unseen refs across 4 seeds, 65 with no DOI; 2 of 4 seeds had citing
  works in OpenCitations.
- Stopping criterion (`SCOPE.md`) **not reached** — the run ended on the time
  budget, with the statement layer built instead of more rounds.

## Citation graph

From `dataset --edges` on the 76-record smoke library:

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

- No seed papers supplied; the harvest runs on `config/queries.txt` alone.
  Resolve any through `harvest --query "<title>"`, never by hand.
- Eight queries were dead or near-dead; rewritten, worth 162 records. arXiv
  matches each concept as a literal phrase, so three-concept ANDs return nothing.

## Decisions made under uncertainty

| Record | Call | Why |
|---|---|---|
| statement layer | extract from all `candidate` papers | 4 screened papers cannot fill 18 subareas |
| relations | keep conditional triples, flagged | dropping them loses the papers' claims |
| test items | no true/false items | flipping `P ⊆ NP` gives an open problem |
| `paper-subarea` items | label is the paper's subareas | a lemma has no subarea of its own |
| single-letter classes | keep `P`, `E`, `L` with guards | dropping them loses `P` vs `NP` |
| e-print fetch rate | 8s, `export.arxiv.org` | arXiv's automation host; no 429 in 750 fetches |

## Run log

- `2026-08-12` — statement layer: 501 papers, 18641 statements, 0 verify errors.
  - `verify --examples` catches a planted reword and a 7-char offset shift.
  - Ten defects found by reading output, none visible in counts; each is now a
    case in `selftest.py` and a line in `README.md` § Traps.
  - Container restarted twice mid-run; cache and stores survived both.
- `2026-08-10` — full harvest: 107 queries at 10s spacing, 0 failures, 2471 records.
  - Five queries returned 0 hits, all in the two thin subareas; rewriting them
    closed both gaps, so those were a grid artifact, not a thin literature.
  - arXiv 429s at the documented 3s floor; `ARXIV_RATE_SECONDS=10` completes clean.
- `2026-08-10` — ported from `lightweight-survey`; subject retargeted, no LLM
  content anywhere.
  - Verified end to end against live arXiv, Crossref, OpenCitations.
  - Gate catches a planted fake DOI and a planted title mismatch; exits 1.
  - Four metadata bugs found and fixed, all worst on old records; see § Traps.
  - Backward snowball from 4 seeds reached 10 pre-2000 papers.
  - Repo golfed: 13 scripts to 4 modules and one CLI.

## What another eight hours would do

- Extract the remaining 1938 papers with an arXiv id; fetch is the only cost.
- Screen the core tier to 100, so `status` can filter the statement layer.
- Two snowball rounds, to test the stopping criterion this run never reached.
