# `prove-sample-2/` — the second bounded prove campaign

A replication of `prove-sample/` on a fresh draw, run through the
`bigodafny-prove-campaign` skill. 50 rows from the 287 in `solutions/` that
carry a label, pass their gate, and had no proof. Seed **20260921**. Three
Sonnet agents, one slice each, **3 attempts and 5 minutes per row**.

**Result: 37 proved, 13 unresolved.** Every proved file was re-verified by
`proofs.py` from scratch — 112/112 files in `solutions-proved/` verify, 0
contain `assume` — and `audit.py` found no disagreement between the agents'
trajectories and the verifier.

## The rate replicates, and so does its shape

| label | drawn | proved | first campaign |
|---|---|---|---|
| `O(n)` | 23 | **20** | 24/24 |
| `O(nlogn)` | 11 | **7** | 5/11 |
| `O(n**2)` | 7 | 3 | 5/6 |
| `O(1)` | 3 | 3 | 4/5 |
| `O(logn)` | 2 | **0** | — |
| `O(n+m)` | 2 | 2 | 3/3 |
| `O(n+m)log(n+m)` | 1 | 1 | — |
| `O(nlogn+mlogm)` | 1 | 1 | — |

37/50 against the first campaign's 40/50 at the same budget. The label-class
effect holds across both draws: **44 of 47 linear rows closed, 12 of 22
`O(nlogn)` rows did**, and neither `O(logn)` row closed in this draw.

The budget is not what decides it. 27 of the 37 proofs closed on the **first
attempt**, median 80 seconds. Rows that close, close quickly; rows that do not
run the clock out.

| obstacle | rows |
|---|---|
| `z3-nonlinear` | 6 |
| `invariant-gap` | 3 |
| `decreases-star` | 2 |
| `budget` | 1 |
| `recursion-depth` | 1 |

Only `1765_40` lost to the clock with the mechanism in hand. `2854_30` and
`457_38` were declined without an attempt and correctly: both carry
`decreases *` in the original, so there is no termination proof to hang a step
bound on, and the campaign rules forbid adding one.

## The finding: a proof caught a translation the tests could not

Two proved bounds sit **below** their label. That direction is the one worth
reading carefully, because it has three possible causes and only one of them
says the label is loose.

| row | label | proved bound | cause |
|---|---|---|---|
| `1243_0` | `O(nlogn+mlogm)` | `4 * \|s1\| + \|s2\| + 2` | translation |
| `2803_133` | `O(n**2)` | `2 * AbsInt(i) + 4` | cost model |

**`1243_0` is a translation-fidelity defect.** The Python decides equality with
`sorted(g1) != sorted(g2)` — that sort is where the `nlogn+mlogm` label comes
from. The Dafny decides it with `multiset(s1) != multiset(s2)`, which the
charge table costs `|s1| + |s2|`. Same output on every test, one asymptotic
class cheaper. This is precisely the trap `CLAUDE.md` names under *Translate
the algorithm, not just the behaviour*, and neither gate can see it: both
compare stdout.

It has two possible remedies and they are not equivalent — re-translate the row
to sort, or reclassify it as disputed. **Left for decision; the row has not
been moved.**

**`2803_133` is the stipulated cost model, working as designed.** `fact(n)`
loops over the input value, so the proof is linear in that value. The `O(n**2)`
label comes from CPython's bignum multiplication, whose cost grows with the
operands' digit count; `COMPLEXITY.md` § 1 charges every `int` operation 1. The
proof and the label are measuring different machines, and the file says so in a
header comment.

Neither row is a `contradicts`. Every bound here is an upper bound, and
`contradicts` is reserved for a source literal that forces more work than the
label allows.

## Value-versus-size after the convention

The first campaign hit the value-versus-size question six times and had to stop.
With the convention settled — a value is a parameter of the bound — it stopped
being a blocker: `1738_24`, `681_105` and `354_95` all closed with the input
value written straight into the bound.

It appears once more as an obstacle rather than a finding. `1944_50` is labelled
`O(n)` and its `CeilSqrt` binary-searches over each element's **value**, so the
real cost is `O(n log v)`. Had it closed it would have been `looser-structural`.
It did not, so it is recorded as unresolved with that note attached.

## Seven rows were excluded from the pool

`excluded.jsonl` lists rows in `solutions/` whose latest recorded gate result is
negative or missing. They were not drawn and are not part of the denominator.

| row | split | recorded gate |
|---|---|---|
| `1196_100`, `1196_51` | strict | no record in `data/validation.jsonl`; older per-batch files say `fail` |
| `1950_45`, `1950_47` | strict | same |
| `1578_481`, `1578_724` | strict | no record anywhere |
| `1501_224` | loose | `differs` (77 of 93 comparable agree) |

Either they were repaired and `validate.py` was never re-run over them, or they
do not belong in the clean partition. **Not investigated here** — it is a
dataset-integrity question, not a proof question.


## Revised 2026-09-23

The prelude gained a composable sort-cost bound and a binary-search potential
(`SortCostNLogN`, `SortCostWithin`, `SearchPot`, `BisectStep`,
`SearchLoopWithin`). With them these rows were re-proved or newly proved, by
hand and outside this campaign's budget:

| row | label | this campaign | now |
|---|---|---|---|
| `1180_626` | O(n+m)log(n+m) | proved, `looser-slack` | proved, `confirms` |
| `2225_154` | O(nlogn) | proved, `looser-slack` | proved, `confirms` |
| `2593_332` | O(nlogn) | proved, `looser-slack` | proved, `confirms` |

**The numbers in this README are unchanged**: they are what a bounded agent
achieved. Each revised trajectory keeps the agent's result as `agent_outcome`,
`agent_relation` and `agent_bound`, and every superseded line — trajectory,
relation, obstacle, audit — is in `old_record.jsonl`, with the file it came
from.

## Files

| file | what it is |
|---|---|
| `manifest.jsonl` | the 50 rows: id, path, label, split, gate |
| `slice_{a,b,c}.jsonl` | the three agent assignments, 17/17/16 |
| `excluded.jsonl` | rows kept out of the pool, with the reason |
| `PROMPT_{a,b,c}.md` | the agent briefs, from the skill's template |
| `traj_{a,b,c}.jsonl` | per-row attempts, bound, timing, failure reason |
| `label_relation.jsonl` | normalised relation per proved row, with reasons |
| `obstacles.jsonl` | coded obstacle per unresolved row |
| `audit.jsonl`, `summary.json` | the verifier-joined audit and its totals |
| `old_record.jsonl` | every line superseded by the 2026-09-23 revision, with its source file |

Proofs are overlay copies in `../../solutions-proved/<pid>/`. The originals in
`solutions/` were not modified; `audit.py` checks that with `git status` rather
than assuming it.
