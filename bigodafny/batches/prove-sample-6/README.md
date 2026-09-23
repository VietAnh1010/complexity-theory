# `prove-sample-6/` — 30 of 50, and the draw had drifted

50 rows from `solutions/` that carry a label, pass their gate, and had no
proof. Seed **20260923**, pool **137**. Three Sonnet agents, one slice each,
**3 attempts and 5 minutes per row**.

**Result: 30 proved, 20 unresolved.**

`proofs.py` re-verified the whole overlay from scratch — **255/255 files
verify, 0 contain `assume`** — and `audit.py` reports no disagreement between
the trajectories and the verifier. `precheck.py` flagged two "unchecked"
clauses on `85_71`; both are inherited from the row itself, not added by the
agent.

## This draw is not comparable with campaign 7

The draw mode was **plain**: every eligible unproved row, including rows an
earlier campaign already drew and failed. **14 of 50 were repeats — 28%.**

| | drawn | proved | rate |
|---|---|---|---|
| never drawn before | 36 | 24 | 67% |
| drawn by an earlier campaign | 14 | 6 | 43% |

A row that fails stays in the pool, so each campaign's plain draw carries more
rows already known to be hard: 8%, 12%, 20%, 28% across campaigns 3 to 6. At
28% the campaign has stopped measuring "can a bounded agent prove a random
row" and started measuring "can a second agent close what a first could not".

Campaign 7 uses `--exclude-drawn` and draws only never-touched rows. Its rate
belongs against campaign 1's, not against this one.

Repeats do not explain the whole drop. The fresh-row rate, 67%, is still below
the 77% pooled over campaigns 1–5. The label mix moved too: **13 `O(n**2)`
rows**, the corpus's hardest class, against 6–11 in every earlier campaign.

## Slices

| slice | drawn | proved |
|---|---|---|
| a | 17 | 10 |
| b | 17 | 15 |
| c | 16 | 5 |

## Rates by label

| label | c1 | c2 | c3 | c4 | c5 | c6 | pooled |
|---|---|---|---|---|---|---|---|
| `O(1)` | 4/5 | 3/3 | 8/8 | 3/4 | 1/1 | 3/4 | 22/25 = **88%** |
| `O(n)` | 24/24 | 20/23 | 12/18 | 21/25 | 22/27 | 11/16 | 110/133 = **82%** |
| `O(n+m)` | 3/3 | 2/2 | 2/2 | — | 1/1 | 3/3 | 11/11 = **100%** |
| `O(nlogn)` | 5/11 | 7/11 | 10/12 | 7/10 | 8/13 | 7/13 | 44/70 = **62%** |
| `O(n**2)` | 5/7 | 3/7 | 6/9 | 7/11 | 4/6 | 5/13 | 30/53 = **56%** |
| `O(logn)` | — | 0/2 | — | — | 0/1 | 1/1 | 1/4 |

Read the pooled column. A single campaign's cell holds 1 to 13 rows, so two
rows move it by double digits. Campaign 3's apparent `O(nlogn)`-over-`O(n)`
crossover did not reproduce in any later campaign.

## Obstacles on the 20 unresolved rows

| obstacle | n |
|---|---|
| `z3-nonlinear` | 8 |
| `value-to-size` | 5 |
| `invariant-gap` | 3 |
| `decreases-star` | 2 |
| `prelude-gap` | 1 |
| `label-mismatch` | 1 |

`z3-nonlinear` is now the leading obstacle and every instance has the same
shape: a quadratic invariant whose `n*n` or `i*n` term needs an isolated
monotonicity or distributivity lemma, not an inline `assert`. That is a
prelude gap wearing a solver's name — the lemmas exist in individual proofs
and have never been lifted.

The three `invariant-gap` rows share one cause too: a parameter that is a trip
count with **no non-negativity precondition** in the row, so the loop
invariant fails on entry. `271_58` is explicit about it — for negative `n` the
row's own early return gives `steps = 3` while `5*n + 10` goes negative.

## Relations on the 30 proved rows

| relation | n |
|---|---|
| `confirms` | 23 |
| `tighter-costmodel` | 3 |
| `looser-slack` | 2 |
| `looser-structural` | 1 |
| `tighter-translation` | 1 |

Every non-`confirms` row was re-read by hand against the Python;
`label_relation.jsonl` carries the reason and the agent's original claim.

## Four findings

**`1948_388` closed.** The project's textbook value-to-size row: one input
number, label `O(1)`, and a `while s*s < target` loop running about
`sqrt(8n+1)` times. Proved `steps <= 32 * n + 5` at the third attempt — loose
against the algorithm's `sqrt`, decisive against the label, which cannot hold.
Moved from `batches/value-bounded-open/` into
`solutions-proved/value-bounded/`, which is now 11 proved and 5 open.

**`647_11` is a translation divergence — flagged, not fixed.** The Python
computes `sum(X[i:n])` inside the loop, which is `O(n)` per iteration and is
where the `O(n**2)` label comes from. The Dafny builds a suffix-sum array in
one pass and is `O(1)` per iteration. Same output, one class cheaper. This is
the same defect as `1243_0`, and the remedy is the same: restore the
per-iteration sum.

**`2254_143` and `2680_221` test the charge table's annotations.** The table
calls `s + [x]` amortised and `s[a..b]` a view. Both hold for Dafny and for a
CPython *list*; neither holds for a CPython *string*, which copies. In both
rows the Python concatenates strings in a loop, so CPython is genuinely one
class slower than the model says. Nothing was changed — the model is
stipulated to be backend-independent, and this is it working as designed —
but the two rows are the concrete cost of that choice.

**`1077_84` is the fifth unreduced-integer-product row**, after `2803_133`,
`1073_645`, `2496_30`'s helper and `1359_4`. `res *= n` with no modulus, so
the value reaches factorial scale while the table charges every `int`
operation 1.

## Effort

| attempts used | rows | of which proved |
|---|---|---|
| 1 | 21 | 13 |
| 2 | 9 | 8 |
| 3 | 20 | 9 |

Median 140 s per row; 7820 s of agent wall clock over the 50.

Nine rows closed only on the third attempt — a fifth of the successes. A
2-attempt budget would have cost those; there is no sign that a 4th would buy
much, since the 20 three-attempt failures name structural obstacles, not
near-misses. `514_140` is the one exception, and says so: its final
coefficient was one arithmetic tweak short.


## Revised 2026-09-23

These rows' records were brought to their latest state after this campaign.
`hand` means proved or tightened by hand, outside any budget, mostly with the
prelude's sort-cost and binary-search lemmas; a campaign name means a later
campaign's bounded agent proved a row this one missed.

| row | label | this campaign | now | by |
|---|---|---|---|---|
| `2105_248` | O(nlogn) | unresolved | proved, `confirms` | hand |
| `499_82` | O(nlogn) | proved, `looser-slack` | proved, `confirms` | hand |
| `514_140` | O(nlogn) | unresolved | proved, `looser-structural` | hand |
| `85_71` | O(nlogn) | proved, `looser-slack` | proved, `confirms` | hand |

**The numbers in this README are unchanged**: they are what this campaign's
bounded agents achieved. Each revised trajectory keeps the agent's result as
`agent_outcome`, `agent_relation` and `agent_bound`, and every superseded line
— trajectory, relation, obstacle, audit — is in `old_record.jsonl`, with the
file it came from.

## Files

| file | what it is |
|---|---|
| `manifest.jsonl` | the 50 drawn rows |
| `excluded.jsonl` | rows skipped at draw time (empty this campaign) |
| `slice_{a,b,c}.jsonl` | the split handed to each agent |
| `PROMPT_{a,b,c}.md` | the brief each agent was given |
| `traj_{a,b,c}.jsonl` | one line per row: outcome, bound, attempts, obstacle |
| `label_relation.jsonl` | hand-checked relations for the non-`confirms` rows |
| `obstacles.jsonl` | the 20 unresolved rows with their obstacle codes |
| `audit.jsonl` | verifier output joined to the trajectories |
| `summary.json` | the counts every number above is drawn from |
| `old_record.jsonl` | every line superseded by the 2026-09-23 revision, with its source file |
