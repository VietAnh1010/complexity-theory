# Scope contract

Re-read before every screening decision. A call not settled here is not
settled — add it here rather than deciding ad hoc.

## In scope

A record belongs if **both** hold:

1. **It is a research paper in computational complexity theory** — it proves,
   constructs, or refutes something about the resources needed to compute.
   Resources: time, space, circuit size, circuit depth, proof length,
   communication, queries, randomness, advice, rounds, non-determinism.
2. **At least one subarea below matches its title or abstract** — what
   `topic.py` checks, and what gates snowballing.

**No year floor.** The load-bearing results are decades old, and backward
snowballing is the only path to them. Nothing may filter by date.

## Out of scope

Recorded in `reason`:

- **`applied`** — an algorithm, system, or experiment with no resource-bound
  claim. Solving an NP-hard problem well in practice is not a complexity result.
- **`combinatorics-only`** — pure combinatorics or algebra a keyword matched.
  Extremal graph theory with no computational model is out.
- **`learning-theory-only`** — sample complexity and PAC with no computational
  resource bound. VC dimension alone does not qualify; computational hardness
  of learning **is** in scope.
- **`not-a-paper`** — errata, corrigenda, retractions, front matter.
- **`unavailable`** — no abstract fetched, so nothing can be judged. A status,
  not a verdict. Never guess an abstract.

Surveys and open-problem lists are **kept**, tagged `survey_signal` — they are
the best snowball seeds available.

## Two tiers

The one departure from the repo this was ported from, which screened every
paper by hand toward a 40-paper target. That does not scale to a dataset.

| Tier | Status | Decided by | Size |
|---|---|---|---|
| Bulk | `candidate` | `topic.py`, automatically | the dataset |
| Core | `included`/`excluded` | reading the abstract against this file | a labeled subset |

The core tier seeds snowballing and measures the automatic gate's precision.
Both export; `status` is a column.

## Subareas

Assigned by `topic.py`, overridable when screening. A paper may hold several:

`circuit-complexity`, `algebraic-complexity`, `proof-complexity`,
`communication-complexity`, `query-complexity`, `derandomization`,
`hardness-of-approximation`, `interactive-proofs`, `fine-grained`,
`parameterized`, `meta-complexity`, `average-case`, `space-complexity`,
`quantum-complexity`, `counting-complexity`, `total-search`, `structural`,
`descriptive-logic`

A record matching none does not enter the library — `in_topic` enforces that.
An unusually high subarea count is either genuine cross-area work or a loose
regex; check.

## Statement layer

What `extract.py` lifts out of a paper's source, and what it leaves.

**In:** theorem, lemma, corollary, proposition, definition, claim, conjecture,
hypothesis, open question, problem, fact, observation, example — the
environments the preamble declares, plus the usual short names when it declares
none.

**Out:**

- **proofs** — the argument, not the claim;
- **remarks and notation** — given a `kind`, then dropped from `KEEP`, so a
  later run can take them without re-parsing;
- **figures, tables, algorithms, bibliographies** — stripped before de-TeXing;
- **bodies under 25 or over 9000 characters** — the second is a mis-parsed
  environment, not a theorem.

A statement carries the terms found *in that statement*. Paper-level usage lives
in `papers/extractions.jsonl` — a paper is about Range Avoidance even when the
theorem stating the bound never names it.

**A relation is a mention, not an assertion.** A triple records that the paper
wrote `A ⊆ B` at that offset. It may be assuming it, refuting it, or deriving it
from a hypothesis; `conditional` marks the last case. Reading `relations` as a
set of established facts is a misreading.

**A statement is a slice, never a summary.** `statement_tex` is the source
between two offsets; `statement_text` is a mechanical de-TeXing of it. Neither
is ever paraphrased, shortened, or written by hand.

## Venues

A signal, never a filter — nothing is excluded for its venue.

**Target:** STOC, FOCS, CCC, SODA, ITCS, ICALP, JACM, SICOMP, Theory of
Computing, *computational complexity*.

**Other:** APPROX, RANDOM, ESA, MFCS, STACS, IPEC, LICS, CSL, QIP, TQC, ITC,
CRYPTO, EUROCRYPT, TCC, TOCT, JCSS, TCS, LMCS, QIC, Combinatorica, CSR.

Preprints are in scope and will be most of the harvest. Where both exist,
`enrich` prefers the published metadata.

**ECCC has no API and is not harvested.** Papers reaching arXiv or a
DOI-bearing venue are picked up then; the rest are invisible. A structural
hole — record it in `STATUS.md`.

## Targets

- Every subarea holds **≥50 papers**; below that, run targeted queries before
  concluding the literature is thin.
- No subarea holds **>25%** of the total. `fine-grained` and `parameterized`
  are the likely offenders — both overlap heavily with cs.DS.
- Every record has an abstract, or is `unavailable`.
- The core tier reaches **100 hand-screened papers** across subareas.

## Stopping

Two consecutive snowball rounds each yielding **<25 new in-scope records**, or
the time budget. Record which in `STATUS.md`: only saturation justifies a
coverage claim.
