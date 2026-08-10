# Scope contract

Re-read before every screening decision. A judgement call not settled here is
not settled — add it here rather than deciding ad hoc mid-run.

## What this repo is

A **dataset of computational complexity theory papers**, mined from public
metadata APIs and exported as flat files. It is not a survey: the deliverable
is `dataset/`, not prose. No claim about the field is made anywhere in this
repo, so no claim has to be defended.

The pipeline is ported from a literature-review repo whose subject was LLMs in
program analysis. **Nothing about LLMs survives that port.** The subject is
complexity theory and only complexity theory; the machinery calls no model and
holds no API key.

## What counts as in scope

A record belongs in the dataset if **both** hold:

1. **It is a research paper in computational complexity theory** — it proves,
   constructs, or refutes something about the resources needed to compute.
   - Resources: time, space, circuit size, circuit depth, proof length,
     communication, queries, randomness, advice, rounds, non-determinism.
2. **At least one subarea below matches its title or abstract.**
   - This is what `scripts/topic.py` checks, and what gates snowballing.

There is **no year floor**. This field's load-bearing results are decades old,
and a dataset that starts at 2020 has no anchors in it. Backward snowballing
is the only path to those papers, so nothing may filter them out by date.

## What is out of scope

Recorded in `reason` when a record is screened out:

- **`applied`** — an algorithm, system, or experiment with no resource-bound
  claim. Solving an NP-hard problem well in practice is not a complexity result.
- **`combinatorics-only`** — a pure combinatorics or algebra paper that a
  complexity keyword happened to match. Extremal graph theory with no
  computational model is out.
- **`learning-theory-only`** — sample-complexity and PAC-learning results with
  no computational resource bound. VC dimension alone does not qualify.
  - Computational hardness of learning **is** in scope; it is a resource bound.
- **`not-a-paper`** — errata, corrigenda, retracted work, duplicate
  submissions, conference front matter.
- **`unavailable`** — no abstract could be fetched, so nothing can be judged.
  This is a status, not a verdict. Never guess an abstract.

Surveys, expository notes, and open-problem lists are **kept**, tagged
`survey_signal`. They are the highest-yield snowball seeds available, and for
a dataset there is no reason to throw them away.

## Two tiers, on purpose

This is the one place the port departs from its source, which screened every
paper by hand toward a 40-paper target. That does not scale to a dataset.

| Tier | Status | How it is decided | Size |
|---|---|---|---|
| **Bulk** | `candidate` | `topic.py` automatically | the dataset |
| **Core** | `included` / `excluded` | read the abstract, judge against this file | a labeled subset |

The bulk tier is the dataset. The core tier does two jobs: it seeds
snowballing, and it is a hand-labeled sample against which the automatic gate's
precision can be measured. Both tiers export; `status` is a column.

**Screen for the core tier from the abstract, never the title.** No abstract
means `unavailable`, not a guess.

## Subareas

Assigned automatically by `scripts/topic.py`, overridable during screening. A
paper may hold several, and many will:

`circuit-complexity`, `algebraic-complexity`, `proof-complexity`,
`communication-complexity`, `query-complexity`, `derandomization`,
`hardness-of-approximation`, `interactive-proofs`, `fine-grained`,
`parameterized`, `meta-complexity`, `average-case`, `space-complexity`,
`quantum-complexity`, `counting-complexity`, `total-search`, `structural`,
`descriptive-logic`

A record matching none of these does not enter the library at all — that is
what `in_topic()` enforces. Records with an unusually high subarea count are
worth a look: they are either genuine cross-area work or a regex that is too
loose.

## Venues

Tracked as `venue_tier: target`, and treated as a quality signal rather than a
filter — nothing is excluded for its venue:

**STOC, FOCS, CCC, SODA, ITCS, ICALP** and the journals **JACM, SICOMP, Theory
of Computing, computational complexity**

Also matched, tracked as `other`: APPROX, RANDOM, ESA, MFCS, STACS, IPEC,
LICS, CSL, QIP, TQC, ITC, CRYPTO, EUROCRYPT, TCC, TOCT, JCSS, TCS,
Combinatorica.

Preprints are in scope and will be most of the harvest. Where a paper has both
a preprint and a published version, `enrich.py` prefers the published metadata.

### The ECCC gap

**ECCC** — the Electronic Colloquium on Computational Complexity — is where
much of this field posts first, and it has **no API**. It is not harvested.
Papers that later reach arXiv or a DOI-bearing venue are picked up then; the
rest are invisible here.

This is a known, structural hole in the dataset. Record it in `STATUS.md`. A
thin subarea is not evidence of a thin literature until this is accounted for.

## Targets

- **Every subarea above holds at least 50 papers.** A subarea below that gets
  targeted queries before anyone concludes the literature is thin there.
- **No subarea holds more than about a quarter of the total.** `fine-grained`
  and `parameterized` are the likely offenders — both overlap heavily with
  cs.DS, which is a large and only partly relevant category.
- **Every record has an abstract**, or is marked `unavailable`. An abstract is
  what makes a record usable for anything downstream.
- **The core tier reaches 100 hand-screened papers**, spread across subareas,
  before snowballing is called done.

## Stopping criteria

Stop harvesting when **two consecutive snowball rounds each yield fewer than
25 new in-scope records**, or when the time budget is spent. Record which one
ended the run in `STATUS.md`: only saturation justifies a coverage claim.
