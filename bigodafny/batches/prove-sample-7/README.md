# `prove-sample-7`

The first fresh-only draw: 50 rows from the 68 that no earlier campaign had
drawn (`--exclude-drawn`, seed `20260923`). Three Sonnet agents per run, 3
attempts and 5 minutes per row.

**Result: 44 proved, 6 unresolved.** Every row has a `reads` trace.

## How the record was assembled

A session rate limit interrupted the first run. The 50 records come from two
runs:

| slice | rows | proved | run |
|---|---:|---:|---|
| `traj_a` | 17 | 14 | original, 2026-09-23 |
| `traj_c2` | 3 | 2 | original, 2026-09-23 |
| `traj_b` | 17 | 16 | rerun, 2026-09-24 |
| `traj_c` | 13 | 12 | rerun, 2026-09-24 |

Slices B and C finished before the `reads` requirement existed. On 2026-09-24
each of their 30 rows was retried from scratch under the same budget
(`rerun/PROMPT_rerun.md`). The agents could not read the row's existing proof,
other solutions of the same problem, or any earlier record. Rerun proofs are in
`rerun/<pid>/<sid>.dfy` and their verifier results in `rerun/verify.jsonl`. The
replaced records, 24 of 30 proved, are in `old_record.jsonl`.

**The two runs used different configurations.** The rerun used the prelude's
sort-cost and binary-search lemmas and the documentation that describes them.
The original run did not. Compare the original configuration using its 50 rows:
40 proved.

## Comparison

Campaigns 1 and 7 are the only draws with no repeated rows:

| campaign | proved |
|---|---:|
| `prove-sample` | 42 / 50 |
| `prove-sample-7`, original run | 40 / 50 |
| `prove-sample-7`, as recorded | 44 / 50 |

Use the original-run figure for a like-for-like comparison.

## Rates by label

| label | proved |
|---|---:|
| `O(n)` | 26 / 26 |
| `O(nlogn)` | 8 / 11 |
| `O(n**2)` | 4 / 6 |
| `O(1)` | 6 / 6 |
| `O(n*m)` | 0 / 1 |

## Unresolved rows

| row | obstacle | run |
|---|---|---|
| `1039_15` | `z3-nonlinear` | original |
| `2128_3` | `z3-nonlinear` | original |
| `2826_81` | `z3-nonlinear` | original |
| `2704_92` | `z3-nonlinear` | original |
| `1718_1166` | `z3-nonlinear` | rerun |
| `281_12` | `decreases-star` | rerun |

Four of the five `z3-nonlinear` rows combine a sort cost with a second
logarithmic or product term. `1039_15`, `2128_3`, `2826_81` and `1718_1166`
were later proved by hand with the prelude lemmas, outside the budget.
`2704_92` fails on a string-length product instead.

`2704_92` recorded 1,500 seconds against the 5-minute limit. It remained
unresolved, so the overrun did not inflate the result.

## Relations of the 44 proofs

| relation | rows |
|---|---:|
| `confirms` | 40 |
| `looser-structural` | 3: `1043_358`, `794_794`, `1678_68` |
| `tighter-costmodel` | 1: `2286_319` |

`1043_358` and `794_794` have loop counts set by input values. They are filed in
`solutions-proved/value-bounded/`. `2286_319` multiplies without a modulus;
the charge table costs each integer operation as one unit.

`1678_68` has two conflicting proofs. The overlay proof charges the recursive
`GcdEx` as one step and proves a constant bound. The rerun charges its
recursion depth, which grows with the input value `rows`. The charge table and
the Python recursion support the rerun, but the overlay proof was not changed.

`2847_36` was a `decreases-star` failure in the original run. The rerun proved
termination without changing the executable code.

## Effort

| attempts used | rows | proved |
|---|---:|---:|
| 1 | 30 | 30 |
| 2 | 11 | 10 |
| 3 | 9 | 4 |

Median time was 110 seconds per row.

## Files

| file | contents |
|---|---|
| `manifest.jsonl`, `excluded.jsonl` | the draw |
| `slice_*.jsonl`, `PROMPT_*.md` | original-run slices and prompts |
| `traj_{a,b,c,c2}.jsonl` | one record per row; B and C are rerun records |
| `rerun/` | rerun slices, prompt, staging records, proofs, and verifier results |
| `label_relation.jsonl`, `obstacles.jsonl` | reviewed relations and obstacle codes |
| `audit.jsonl`, `summary.json` | verifier results joined to records |
| `old_record.jsonl` | superseded records |
