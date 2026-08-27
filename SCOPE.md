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

**One alternative to (1), for `verification-complexity` only.** There the
resource is the cost of *checking* a program, and a paper qualifies by claiming
a bound on it in either sense:

- **Theoretical** — decidability, a decision-procedure complexity, a fragment
  that is or is not tractable, an unavoidable blow-up.
- **Measured** — analysis cost on real code: lines analysed, proof or
  annotation burden, what modularity or incrementality buys.

The second is a departure. A Frama-C or Dafny paper reporting that a technique
holds up on a million-line codebase makes a resource claim about verification
even when it proves no theorem, and that claim is the reason this subarea
exists. `topic.py:VERIF_TERMS` is the gate; `in_topic` applies it to this
subarea and no other, so the other seventeen keep the original conjunction.

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
- **`toy-scale`** — `verification-complexity` only: a tool demo or case study
  on one small program, with neither a complexity claim nor a cost measurement.
  Verifying a linked list in Dafny is not a scalability result.
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
`descriptive-logic`, `verification-complexity`

A record matching none does not enter the library — `in_topic` enforces that.
An **excluded** record may still end up matching none: the gate is tightened when
a query grid pulls in a neighbouring field, and what it already admitted stays.
`stats.json` counts `uncategorized` over everything the gate still admits.
An unusually high subarea count is either genuine cross-area work or a loose
regex; check.

## Venues

A signal, never a filter — nothing is excluded for its venue.

**Target:** STOC, FOCS, CCC, SODA, ITCS, ICALP, JACM, SICOMP, Theory of
Computing, *computational complexity*. For `verification-complexity` also
CAV, POPL, PLDI, OOPSLA, TACAS, VMCAI, CADE, IJCAR, ITP, CPP, FM, ICSE, TOPLAS,
JAR — the tools live there, not in the complexity venues.

**Other:** APPROX, RANDOM, ESA, MFCS, STACS, IPEC, LICS, CSL, QIP, TQC, ITC,
CRYPTO, EUROCRYPT, TCC, TOCT, JCSS, TCS, LMCS, QIC, Combinatorica, CSR; and for
the verification tier SAS, ESOP, FMCAD, SAT, LPAR, FMSD, FSE, TSE, TOSEM.

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
- In `verification-complexity`, every `included` record is tagged with whether
  the idea is known to run on a large codebase: `scales-large`, `scales-unclear`,
  or `theory-only`. The tag, not the status, is what makes the subarea useful.

## Stopping

Two consecutive snowball rounds each yielding **<25 new in-scope records**, or
the time budget. Record which in `STATUS.md`: only saturation justifies a
coverage claim.
