# `prove-sample-3/` — 39 of 50, and one claim that did not hold

> **Correction, 2026-09-21.** This file was titled "the label stops predicting
> difficulty" and argued that `O(nlogn)` had overtaken `O(n)`. **Campaign 4 did
> not reproduce it.** `O(n)` came back at 21/25 and `O(nlogn)` at 7/10; pooled
> over four campaigns they are 86% and 66%, which is campaign 1's ordering.
> The crossover below was read off two swings in cells of 12 to 18 rows. The
> section is kept as written, with its numbers intact, because the error is
> worth seeing; the conclusion it draws is withdrawn. What did hold is the
> `value-to-size` obstacle, which campaign 4's agents named independently.

50 rows from the 250 in `solutions/` that carry a label, pass their gate, and
had no proof. Seed **2026092102**. Three Sonnet agents, one slice each,
**3 attempts and 5 minutes per row**.

**Result: 39 proved, 11 unresolved.** `proofs.py` re-verified the whole overlay
from scratch — 151/151 files verify, 0 contain `assume` — and `audit.py` found
no disagreement between the trajectories and the verifier. `precheck.py`
checked all 39 proved rows' preconditions against real inputs: 64 clauses, 0
violated.

## The finding: what is hard has changed

| label | campaign 1 | campaign 2 | campaign 3 | all |
|---|---|---|---|---|
| `O(n)` | **24/24** | 20/23 | **12/18** | 56/65 |
| `O(nlogn)` | **5/11** | 7/11 | **10/12** | 22/34 |
| `O(n**2)` | 5/6 | 3/7 | 6/9 | 14/22 |
| `O(1)` | 4/5 | 3/3 | 8/8 | 15/16 |
| `O(n+m)` | 3/3 | 2/2 | 2/2 | 7/7 |
| `O(logn)` | — | 0/2 | — | 0/2 |

Campaign 1's headline was that the label predicts difficulty: linear rows were
free, `O(nlogn)` was where the budget went. **Three campaigns in, the two have
crossed over.** `O(nlogn)` went 5/11 → 7/11 → 10/12 while `O(n)` went 24/24 →
20/23 → 12/18.

The reason is that the two difficulties are not the same kind of thing.

`O(nlogn)` was hard because of **scaffolding**: the recursion-tree argument
over a ceiling log, with every multiplication isolated into its own lemma.
That is a fixed cost, paid once. By this campaign the corpus carried both the
`SortCost` scaffold and the tight `CeilLog2` argument, and agents copied them.

The linear failures are not like that. Four of the eleven unresolved rows fail
on the same thing, and it is not reusable:

| obstacle | rows |
|---|---|
| `value-to-size` | 4 |
| `z3-nonlinear` | 3 |
| `decreases-star` | 2 |
| `invariant-gap` | 2 |

**`value-to-size`** is a new code, and it is not the value-versus-size question
the convention settled. That question was *how to count* a value-bounded loop,
and it is answered: the value is a parameter. This is the next one — how to
**connect** a value-bounded cost back to a bound in the row's size:

- `1047_26` — `NumToLetters` recurses on an int value; folding its charge back
  to the cell length needs `colNum < Pow10(maxlen)` chained through `Pow10Mono`
  into the loop invariant.
- `1944_50` — `CeilSqrt` doubles to find `hi`, then bisects; tying the
  per-iteration `Pow2`/`Log2` growth to the list length did not close.
- `2423_48` — the outer loop is bounded by the maximum first component of the
  pairs, so the `ensures` needs a ghost `MaxFirst` plus a proof it equals the
  last element of `d`.
- `2819_926` — `RepStr` is called on `x-y-1` and `y`, derived through
  `FloorDiv` and a triangular number; four or five chained nonlinear
  inequalities would be needed to bound them by `nn` and `k`.

Each needs its own arithmetic lemma. Nothing carries from one row to the next,
which is exactly why the rate is not improving the way `O(nlogn)`'s did.

The two `decreases-star` rows are the corpus's own backlog surfacing again:
`457_38` and `2854_30` carry `decreases *` in the original, so there is no
termination proof to hang a step bound on. Both failed in campaign 2 as well.

## Relations

| relation | rows | |
|---|---|---|
| `confirms` | 30 | the bound is within the label's class |
| `looser-slack` | 5 | the quadratic `SortCost` scaffold, tight bound not attempted |
| `looser-structural` | 3 | the proof exposes a cost the label omits |
| `tighter-costmodel` | 1 | the charge table costs something CPython does not |

All nine non-`confirms` rows were re-read against their Python before being
accepted; every agent assignment stood. The 30 `confirms` rows were checked too
— each one's `Solve` bound read off the file and compared against its label.

The three `looser-structural` rows are all value-bounded, and they are the same
finding as the obstacle above seen from the other side — these closed:

- `305_76` — the loop runs from `min(d_list)-1` down toward `2*min(c_list)`, an
  iteration count bounded by a gap between input **values**.
- `704_351` — fuel seeded from `(240-b)/5`; the honest bound is `O(b)`, and the
  `O(1)` label holds only under Codeforces's unstated `0 <= k <= 240` cap.
- `1867_16` — the `'1'`-run length is `t - A[x-1]`, an unbounded input value
  per query.

`1073_645` is `tighter-costmodel`: `Factorial(a)` recurses `a` times at 1 per
operation, giving `O(n)` where the label says `O(n**2)`. The label counts
CPython multiplying n-digit bignums; `COMPLEXITY.md` § 1 charges every `int`
operation 1. Same cause as `2803_133` in campaign 2.

## The run was interrupted

A session rate limit killed all three agents mid-slice, with 34 of 50 rows
recorded. They were resumed on the 16 remaining rows only, appending to their
existing trajectories.

Two rows had partial proof copies left behind — `2926_54` and `2496_30`.
Neither verified. Both were deleted and the rows redone from scratch, so no
half-written proof could be counted as a closed one.

`2926_54` is worth noting: campaign 2 drew it too and failed on it. It closed
here. `457_38`, also drawn twice, failed both times for the same reason.

## Budget

24 of the 39 proofs closed on the **first attempt**; median 90 seconds, longest
260. As in both earlier campaigns, rows that close, close quickly. Not one of
the eleven failures was a budget failure — every one names a specific obstacle.


## Revised 2026-09-23

These rows' records were brought to their latest state after this campaign.
`hand` means proved or tightened by hand, outside any budget, mostly with the
prelude's sort-cost and binary-search lemmas; a campaign name means a later
campaign's bounded agent proved a row this one missed.

| row | label | this campaign | now | by |
|---|---|---|---|---|
| `1047_26` | O(n) | unresolved | proved, `confirms` | `prove-sample-5` |
| `1333_127` | O(nlogn) | proved, `looser-slack` | proved, `confirms` | hand |
| `1359_4` | O(n**2) | unresolved | proved, `tighter-costmodel` | `prove-sample-5` |
| `1453_211` | O(nlogn) | proved, `looser-slack` | proved, `confirms` | hand |
| `1820_180` | O(n) | unresolved | proved, `looser-structural` | `prove-sample-4` |
| `2072_40` | O(nlogn) | unresolved | proved, `confirms` | `prove-sample-6` |
| `2423_48` | O(nlogn) | unresolved | proved, `looser-structural` | hand |
| `2496_30` | O(nlogn) | proved, `looser-slack` | proved, `confirms` | hand |
| `2725_319` | O(nlogn) | proved, `looser-slack` | proved, `confirms` | hand |
| `3070_180` | O(nlogn) | proved, `looser-slack` | proved, `confirms` | hand |

**The numbers in this README are unchanged**: they are what this campaign's
bounded agents achieved. Each revised trajectory keeps the agent's result as
`agent_outcome`, `agent_relation` and `agent_bound`, and every superseded line
— trajectory, relation, obstacle, audit — is in `old_record.jsonl`, with the
file it came from.

## Files

| file | what it is |
|---|---|
| `manifest.jsonl` | the 50 rows: id, path, label, split, gate |
| `slice_{a,b,c}.jsonl` | the three agent assignments, 17/17/16 |
| `resume_{a,b,c}.jsonl` | the 16 rows left after the interruption |
| `PROMPT_{a,b,c}.md`, `PROMPT_resume_{a,b,c}.md` | the agent briefs |
| `traj_{a,b,c}.jsonl` | per-row attempts, bound, timing, failure reason |
| `label_relation.jsonl` | normalised relation per proved row, with reasons |
| `obstacles.jsonl` | coded obstacle per unresolved row |
| `audit.jsonl`, `summary.json` | the verifier-joined audit and its totals |
| `old_record.jsonl` | every line superseded by the 2026-09-23 revision, with its source file |

Bounds in `label_relation.jsonl` are read from each file's `Solve` method, not
from `data/complexity_proofs.jsonl`: `proofs.py`'s `bound_of` takes the first
`ensures steps <=` in a file, which is a helper's in 7 of the 151 proofs.
