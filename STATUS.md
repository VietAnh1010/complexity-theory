# Status

Live run state. **Update after every batch, then commit.** This file plus the
git log is the entire handoff.

## Current

- **Phase:** complete for this run; dataset exported, gate clean
- **Last updated:** 2026-08-25
- **Next action:** screen the remaining 520 verification candidates, then round 4

Stopped on **time budget**, not saturation: snowball yielded 156, 51, 48 new
records across three rounds, never twice under 25.

## Counts

From `dataset/stats.json` after `run.py dataset --edges`.

| | |
|---|---|
| papers | 3164 |
| with an abstract | 3106 |
| with a DOI | 1908 |
| uncategorized | 0 |
| core tier | 121 included, 12 excluded, 17 unavailable |

Subareas: `verification-complexity` 658 (20.8%, under the 25% cap), every
subarea over 50, smallest `meta-complexity` at 60.

Core tier by scale verdict — the tag, not the status, is the answer to "does
this work on a large codebase":

| tag | n | what it means |
|---|---|---|
| `theory-only` | 73 | decidability or complexity result, no code |
| `scales-unclear` | 35 | technique with benchmark-scale evidence only |
| `scales-large` | 8 | run on a real codebase, with numbers |
| untagged | 5 | the four pre-existing complexity records |

The eight `scales-large`: CEGAR, bi-abduction, LOCKSMITH, incremental CodeQL,
symbolic partial-order execution, Goanna, automotive abstract interpretation,
agentic separation-logic spec synthesis.

## Snowball rounds

| Round | Direction | Seeds | Seeds w/o DOI | New |
|---|---|---|---|---|
| smoke | both | 4 | 0 | 39 |
| 1 | both | 56 | 2 | 156 |
| 2 | both | 101 | 12 | 51 |
| 3 | both | 121 | 14 | 48 |

Round 3 backward yielded 6 new against 2330 unseen refs: the reference sets of
these seeds are largely inside the library already. Forward is what still pays.

Smoke round reach: 92 unseen refs across 4 seeds, 65 refs with no DOI; 2 of 4
seeds had citing works in OpenCitations.

Stopping criterion (`SCOPE.md`): two consecutive rounds each under 25 new.

## Citation graph

From `run.py dataset --edges` on the 3164-record library:

| | |
|---|---|
| edges | 2716 |
| papers queried | 1819 |
| papers without a DOI | 1256 |
| papers Crossref has no references for | 89 |
| references seen | 60283 |
| deposited unstructured | 16044 |
| pointing outside the library | 41408 |

27% of references are deposited as plain text and are invisible to Crossref.
**85 of the 89 papers with no reference data are LIPIcs** (`10.4230`): those
DOIs are registered with DataCite, so Crossref 404s them. LIPIcs is ITCS, CCC,
ICALP, STACS, MFCS, ESA, IPEC — a hole in the graph shaped exactly like the
target venues, and a second structural gap alongside ECCC.

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
| 17 with no abstract | `unavailable` | ACM/IEEE/Springer deposit none; several are on target, e.g. scalable shape analysis for systems code |
| `linsyn2022` | included, p1 | neural-network certification, not code; a cost claim, so in, but doubt is in the reason |
| LLM-for-verification papers | screened like any other | spec synthesis with a measured burden is in; a benchmark of 77 algorithms is `toy-scale` |
| FO model checking papers | categories overridden | Courcelle-style meta-theorems moved to `parameterized`/`descriptive-logic`, off the verification tier |
| `Faster FPT Algorithms…` DOI | kept | title differs by one word from the published version, but the authors match |

## Run log

- `2026-08-25` — screened 142 records; core tier 4 -> 121 included.
  - 109 of the 121 are `verification-complexity`; 83 are at a target venue.
  - Snowball reached the anchors keyword search cannot: CEGAR (2003),
    Nelson-Oppen (1979), congruence closure (1980), Cook-style relative
    completeness (1978), bi-abduction (2011), abstract-interpretation
    completeness (2000).
  - 17 records are `unavailable`: no abstract deposited, no arXiv preprint.
    - All ACM, IEEE, Springer or Elsevier. Nine landed in one batch.
    - This is where the tier loses most: the pre-2015 tool papers are exactly
      the ones with no abstract.
- `2026-08-25` — two live metadata bugs, both found by running the gate.
  - MFCS matched the `FOCS` pattern and was promoted to target tier.
    - Same shape as ECCC before CC; the fix is ordering plus a note.
  - `tsim >= .8` assigned one paper another paper's DOI.
    - "Parameterised Complexity of X" vs "Complexity of X": overlap .875.
    - Replaced by `title_match`; `enrich` re-checks and clears, 48 cleared.
    - Tuned against the 114 pairs the first attempt flagged. 53 were accent or
      LaTeX drift, 17 an empty Crossref title, 38 genuinely wrong.
  - `verify --all`: 0 errors, 11 warnings, all preprint-vs-published years bar
    one ACM DOI registered ahead of publication.

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
