# `prove-sample-7/` — 40 of 50, the first fresh-only draw

50 rows drawn with `--exclude-drawn` from the **68 rows no earlier campaign
had touched**. Seed **20260923**. Three Sonnet agents, one slice each,
**3 attempts and 5 minutes per row**.

**Result: 40 proved, 10 unresolved.**

`proofs.py` re-verified the whole overlay from scratch — **295/295 files
verify, 0 contain `assume`** — and `audit.py` reports no disagreement between
the trajectories and the verifier.

## This is the campaign that is comparable with campaign 1

Campaigns 2–6 drew plainly, so each carried more rows an earlier campaign had
already failed: 4%, 10%, 12%, 24%, 28%. This draw carries none. Rows never
drawn were never selected on — earlier campaigns removed a random part of the
pool (what they proved) and left a non-random part (what they failed), so the
never-drawn remainder still looks like the original population.

| all-fresh campaign | drawn | proved | rate |
|---|---|---|---|
| `prove-sample` (c1) | 50 | 42 | 84% |
| `prove-sample-7` (c7) | 50 | 40 | 80% |

Four points apart on 50 rows each is not a finding. What it does establish is
that **the decline across campaigns 2–6 was the draw, not the agents**: the
plain-draw rates fell to 60% by c6 while the fresh-row rate held.

## Slices, and a run that had to be restarted

| slice | drawn | proved |
|---|---|---|
| a | 17 | 14 |
| b | 17 | 14 |
| c | 13 | 10 |
| c2 | 3 | 2 |

A session rate limit killed all three agents mid-run. Slice B finished; slice
C stopped at 13 of 16 and its last 3 rows ran later as `c2`; slice A had
written one trajectory line and left 14 `.dfy` files with no record behind
them. Those 14 were **discarded, not kept**, and slice A was re-run from
scratch — a proof with no trajectory has no attempt count, no elapsed time and
no reading trace, and none of that can be recovered afterwards. Left in place
they would also have handed the re-run agent a finished proof of its own
assigned row.

## Rates by label

| label | drawn | proved | rate |
|---|---|---|---|
| `O(n)` | 26 | 24 | 92% |
| `O(nlogn)` | 11 | 7 | 64% |
| `O(n**2)` | 6 | 3 | 50% |
| `O(1)` | 6 | 6 | 100% |
| `O(n*m)` | 1 | 0 | — |

The ordering is the one campaign 1 found and every pooled table since has
kept: `O(1)` and `O(n)` close easily, `O(nlogn)` and `O(n**2)` do not. Read
`data/prove_stats.md` for the pooled column; a single campaign's cell moves
ten points on two rows.

## One gap accounts for eleven of the fifty rows

This is the campaign's finding, and it is not a fact about the agents.

**Six proved rows are `looser-slack` for one reason**: `223_3085`, `2514_221`,
`952_163`, `209_103`, `2198_52`, `566_183` all reused the opaque `SortCost`
scaffold, which bounds merge sort by O(k²), instead of the tight `CeilLog2`
recursion tree. Each proved O(n²) on an `O(nlogn)` row. The label is not in
question; the proof did not reach it.

**Five of the seven `z3-nonlinear` failures are the same shape**: a sort's cost
summed with a second, independent term — a per-iteration binary search, a
second sort, or a size fold — in one postcondition. `1039_15`, `2128_3`,
`2826_81`, `1387_19` and `1718_1166` all died there. (An earlier version of
this file also counted `2704_92`; its obstacle is a string-length product
`|s0| * iters`, not a sort, so the count was twelve and is eleven.)

So **11 of 50 rows were limited by one missing prelude lemma**: a reusable
tight merge-sort cost bound that composes.

**Resolved on 2026-09-23.** The prelude now carries it: `SortCost`, an opaque
`NLogN`, `SortCostNLogN`, `SortCostWithin`, and a binary-search potential
(`SearchPot`, `BisectStep`, `SearchLoopWithin`). With them, by hand and
outside the budget:

- the six `looser-slack` rows now prove O(n log n), `confirms`;
- the five sort-shaped failures are proved — four `confirms`, and `1718_1166`
  `looser-structural`, since its O(n*m) label omits the two full-list sorts
  the Python really does.

The campaign's own numbers above are unchanged: they are what a bounded agent
achieved. Each revised row keeps the agent's result as `agent_outcome`, and
every superseded line is in `old_record.jsonl`.

`2128_3` is the sharpest version. Its agent **found a working proof on a 4th
edit** — hoisting the repeated `CeilLog2(n)` into one ghost variable and
inserting named intermediate asserts instead of one final combine — and
discarded it, recording `unresolved`, because the budget is 3 attempts. That
is the rule working: the measurement is what a bounded agent achieves, not
what one could achieve given more.

## Obstacles on the 10 unresolved rows

| obstacle | n |
|---|---|
| `z3-nonlinear` | 7 |
| `decreases-star` | 2 |
| `budget` | 1 |

Only one row ran out of budget on arithmetic rather than structure:
`2913_484`, whose `ensures` was off by the `+2` post-loop output charge.

## Relations on the 40 proved rows

| relation | n |
|---|---|
| `confirms` | 31 |
| `looser-slack` | 6 |
| `looser-structural` | 2 |
| `tighter-costmodel` | 1 |

Every non-`confirms` row was re-read against the Python;
`label_relation.jsonl` carries the reason and the agent's original claim.

**`1043_358` and `794_794` are value-bounded** and were filed into
`solutions-proved/value-bounded/`, which is now thirteen rows. Both are the
plainest form: `1043_358` prints `"2" + "3" * (v - 1)` per test case, so the
work per test is the input value; `794_794` loops `range(1, n)` where `n` is a
per-test value, while the label's `n` counts test cases.

**`2286_319` is the sixth unreduced-integer-product row**, after `2803_133`,
`1073_645`, `2496_30`'s helper, `1359_4` and `1077_84`. `fac(x)` runs `p *= i`
with no modulus, so the value reaches factorial scale while the charge table
costs every `int` operation 1.

## A row the vocabulary has no word for

`888_6` proved at `60*n + |output| + 50` — **O(n) against an `O(n**2)`
label**. A bound below the label has three recognised causes, and this is none
of them:

- not `tighter-translation`: the Python is a two-pointer sweep whose `p` and
  `q` advance monotonically over `2n` elements and never reset, and the Dafny
  mirrors it statement for statement;
- not `tighter-costmodel`: no integer here grows past a machine word.

The label is simply loose. An O(n) upper bound sits inside O(n²), so
`confirms` is correct by the vocabulary's own definition — but it records
nothing about a label that overstates by a full class. **The vocabulary has no
value for that**, and the same silence would fall on any row whose profiled
label is a class too high. Worth adding before it recurs.

## Effort

| attempts used | rows | of which proved |
|---|---|---|
| 1 | 29 | 27 |
| 2 | 10 | 10 |
| 3 | 11 | 3 |

Median 100 s per row; 7700 s of agent wall clock over the 50.

Two-thirds of the proofs closed on the first attempt, and **every row that
reached a second attempt closed on it**. The third attempt returned 3 of 11.
The budget is spent in the right place: a row that does not fall out quickly
usually does not fall out at all.

## Reading traces

New this campaign, and only partly collected: **20 of 50 rows** carry one —
slice A's 17 and C2's 3, the slices that ran after the requirement was added.
Slice B's 17 and slice C's first 13 finished before it existed and were **not
backfilled**, because a trace is a record of what an agent opened and cannot
be reconstructed after the fact.

Of the 42 entries recorded, 21 name the source row, 20 a prelude declaration
and 1 a helper. Median depth 2, maximum 3. The prelude functions agents
actually had to open: `IntToString` 5, `Join` 3, `Sort` 3, `FloorDiv` 2, then
`AbsInt`, `MinSeq`, `FloorMod` and `SortInts` once each.


## Revised 2026-09-23

The prelude gained a composable sort-cost bound and a binary-search potential
(`SortCostNLogN`, `SortCostWithin`, `SearchPot`, `BisectStep`,
`SearchLoopWithin`). With them these rows were re-proved or newly proved, by
hand and outside this campaign's budget:

| row | label | this campaign | now |
|---|---|---|---|
| `1039_15` | O(nlogn) | unresolved | proved, `confirms` |
| `1387_19` | O(nlogn) | unresolved | proved, `confirms` |
| `1718_1166` | O(n*m) | unresolved | proved, `looser-structural` |
| `209_103` | O(nlogn) | proved, `looser-slack` | proved, `confirms` |
| `2128_3` | O(nlogn) | unresolved | proved, `confirms` |
| `2198_52` | O(nlogn) | proved, `looser-slack` | proved, `confirms` |
| `223_3085` | O(nlogn) | proved, `looser-slack` | proved, `confirms` |
| `2514_221` | O(nlogn) | proved, `looser-slack` | proved, `confirms` |
| `2826_81` | O(nlogn) | unresolved | proved, `confirms` |
| `566_183` | O(nlogn) | proved, `looser-slack` | proved, `confirms` |
| `952_163` | O(nlogn) | proved, `looser-slack` | proved, `confirms` |

**The numbers in this README are unchanged**: they are what a bounded agent
achieved. Each revised trajectory keeps the agent's result as `agent_outcome`,
`agent_relation` and `agent_bound`, and every superseded line — trajectory,
relation, obstacle, audit — is in `old_record.jsonl`, with the file it came
from.

## Files

| file | what it is |
|---|---|
| `manifest.jsonl` | the 50 drawn rows |
| `excluded.jsonl` | rows skipped at draw time: 237 already proved, 39 drawn before |
| `slice_{a,b,c}.jsonl`, `slice_c2.jsonl` | the split handed to each agent |
| `PROMPT_{a,b,c,c2}.md` | the brief each agent was given |
| `traj_{a,b,c,c2}.jsonl` | one line per row: outcome, bound, attempts, obstacle, reads |
| `label_relation.jsonl` | hand-checked relations for the 10 rows needing one |
| `obstacles.jsonl` | the 10 unresolved rows with their obstacle codes |
| `audit.jsonl` | verifier output joined to the trajectories |
| `summary.json` | the counts every number above is drawn from |
| `old_record.jsonl` | every line superseded by the 2026-09-23 revision, with its source file |
