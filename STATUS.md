# Status

Live run state. **Update after every batch, then commit.** This file plus the
git log is the entire handoff.

## Current

- **Phase:** statement layer built over 501 papers; paper layer unchanged
- **Last updated:** 2026-08-12
- **Next action:** `run.py extract --limit 500` to widen; core-tier screening is
  still at 4 papers

Coverage targets in `SCOPE.md` all met on the paper layer: every subarea over
50, largest at 20%, 0 uncategorized, 2455 of 2471 with an abstract.

**Push is blocked.** GitHub access in this session is read-only — `git push` and
the GitHub API both return 403 `Resource not accessible by integration`. Every
commit is local on `claude/extract-datasets-papers-8zdhcf`. An admin can grant
write access in the Claude GitHub settings (https://claude.ai/admin-settings/claude-in-slack).

## Counts

_Refresh with `run.py dataset` and `run.py examples`, then read the two stats files._

| | |
|---|---|
| papers in library | 2471 |
| papers with arXiv source extracted | 501 |
| statements extracted | 18641 |
| test items derived | 3207 |
| distinct complexity classes named | 164 |

Statements by kind: lemma 4995, theorem 4454, definition 4100, proposition
1377, corollary 1360, claim 922, then fact, example, observation, problem,
open-question, conjecture, hypothesis.

Every subarea holds **≥1000 statements** — selection is round-robin across
subareas, so nothing is starved. Largest is `quantum-complexity` at 3116.

## Statement layer reach

| outcome | papers |
|---|---|
| `ok` — source parsed | 495 |
| `gone` — arXiv has no source | 3 |
| `pdf-only` — no LaTeX in the submission | 2 |
| `error` | 1 |
| source parsed, no theorem environments | 8 |

- 32 of 2471 library papers carry **no arXiv id at all** and this layer cannot
  reach them; they are the pre-2000 anchors snowballing found, plus journal-only
  records. That gap is structural, not a parser failure.
- The 8 zero-yield papers state their results in prose, not in environments.
- Median 30 statements per paper.

## Field coverage within statements

| field | statements |
|---|---|
| bounds | 6072 |
| classes | 2651 |
| problems | 2175 |
| measures | 384 |
| hypotheses | 300 |
| problem specifications | 288 |
| class relations | 227 |

- 280 relation triples; **168 of them are conditional** — "unless NP ⊆ coNP/poly"
  is the commonest shape in the parameterized papers.
- Most statements carry no class name at all: query, communication and
  algebraic papers state results in measures (`R(f)`, `Q(f)`, `deg`) and bounds.

## Known precision limits

- **One-letter class names are the noisy field.** `E` and `L` are also an edge
  set and a language variable in half the papers that use them. Guards reject
  expectations, norms, Euler's number and bound variables; some survive.
  Multi-letter names are reliable.
- **`statement_text` is lossy.** Author macros defined in a `.sty` that arXiv
  did not ship stay as bare command names. `statement_tex` is exact.
- **The bulk tier is unscreened.** 2467 of 2471 papers are `candidate`, so the
  statement layer includes preprints announcing resolutions of P vs NP. Filter
  on `status` when that matters.

## Snowball rounds

| Round | Direction | Seeds | Seeds w/o DOI | New |
|---|---|---|---|---|
| smoke | both | 4 | 0 | 39 |

Smoke round reach: 92 unseen refs across 4 seeds, 65 refs with no DOI; 2 of 4
seeds had citing works in OpenCitations.

Stopping criterion (`SCOPE.md`): two consecutive rounds each under 25 new. **Not
reached** — the run ended on the time budget, with the statement layer built
instead of more snowball rounds.

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

- No seed papers supplied; the harvest runs on `config/queries.txt` alone.
  - Resolve any through `run.py harvest --query "<title>"`.
  - Never enter one by hand into the library.
- Eight queries were dead or near-dead; rewritten and re-run, worth 162 records.
  - arXiv matches each concept as a literal phrase.
  - Three-concept ANDs and LaTeX-written class names return nothing.

## Decisions made under uncertainty

| Record | Call | Why |
|---|---|---|
| statement layer | extract from all `candidate` papers, not only screened ones | 4 screened papers cannot fill 18 subareas |
| relations | keep conditional triples, flagged | dropping them loses the papers' actual claims |
| test items | no true/false items | flipping `P ⊆ NP` gives an open problem, not a falsehood |
| `paper-subarea` items | label is the paper's subareas | a lemma has no subarea of its own; named so |
| single-letter classes | keep `P`, `E`, `L` with guards | dropping them loses `P` vs `NP` and `L` vs `NL` |
| e-print fetch rate | 8s, `export.arxiv.org` | arXiv's automation host; no 429 in 750 fetches |

## Run log

- `2026-08-12` — statement layer: 501 papers fetched, 18641 statements, 0 verify
  errors.
  - `verify --examples` re-derives each statement from the cached tarball and
    compares byte for byte; catches a planted reword and a 7-char offset shift.
  - Ten defects found by reading output, none visible in counts. Each is now a
    case in `scripts/selftest.py`:
    - `\ensuremath` missing from the font list hid every class written `\cc{…}`.
    - Case folding made the word "circuit" the class CIRCUIT.
    - `{\rm P}` (pre-2005 style) was invisible; those are the anchor papers.
    - `\xspace` between a class and `\subseteq` blocked every relation.
    - Dropping `∩ Π_2E` from an intersection changes the claim, not its strength.
    - `\mathrm{\bm{\newmathbb{E}}}` read as the class E; so did `\mathrm{e}`.
    - `L^2(G)` counted its exponent as a letter and passed as a class.
    - Conditionals were recorded as assertions.
    - `P_{classical} = P_{observer}` flattened to the tautology `P = P`.
    - LyX's `\newtheorem{thm}{\protect\theoremname}` disabled the default
      mapping, dropping every statement in those papers.
- `2026-08-11` — container restarted mid-fetch; the cache and stores survived and
  the run resumed with no loss. `extract` saves every 5 papers.
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
- `2026-08-10` — first full harvest hit arXiv 429s after ~30 queries at the
  documented 3s floor.
  - Fixed by `ARXIV_RATE_SECONDS`; a full grid at 10s completes clean.
  - Harvest now saves every 5 queries; it previously saved only at the end.
- `2026-08-10` — repo golfed: 13 scripts to 4 modules and one CLI.
- `2026-08-10` — full harvest: 107 queries at 10s spacing, 0 failures, 2471 records.
  - Five queries returned 0 hits and mapped onto the two thin subareas.
    - `total-search` and `descriptive-logic` were a grid artifact, not a thin
      literature. Rewriting the queries closed both gaps.

## What another eight hours would do

- Extract the remaining 1938 papers with an arXiv id — the fetch is the only
  cost, at 8s each, and the parser handles ~1 paper/second.
- Screen the core tier to 100 papers, so `status` can filter the statement layer.
- Two snowball rounds, to test the stopping criterion that this run never reached.
