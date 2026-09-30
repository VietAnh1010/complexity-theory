# `prove-sample-7`

The first fresh-only draw: 50 rows from the 68 that no earlier campaign had
drawn (`--exclude-drawn`, seed `20260923`). Three Sonnet agents per run, 3
attempts and 5 minutes per row.

**Result: 44 proved, 6 unresolved.** Every row has a `reads` trace.

## How the record was assembled

A session rate limit interrupted the first run, and its slices B and C finished
before the `reads` requirement existed. On 2026-09-24 those 30 rows were
retried from scratch under the same budget, in new slices RA, RB and RC
(`PROMPT_rerun.md`). The rerun agents could not read the row's existing proof,
other solutions of the same problem, or any earlier record.

Each row has exactly one record, in the trajectory of the slice that produced
it:

| slice | rows | proved | run |
|---|---:|---:|---|
| `a` | 17 | 14 | original, 2026-09-23 |
| `c2` | 3 | 2 | original, 2026-09-23 |
| `ra` | 10 | 10 | rerun, 2026-09-24 |
| `rb` | 10 | 8 | rerun, 2026-09-24 |
| `rc` | 10 | 10 | rerun, 2026-09-24 |

All 28 rerun proofs are in `solutions-proved/`. 24 compiled to their row's
Python as written. 4 changed the row's code and were fixed by the main agent on
2026-09-29 before promotion; each record says what in
`rerun.fixed_before_promotion`:

| row | agent's change | fix |
|---|---|---|
| `794_794` | non-ghost counter `cnt3` | made ghost |
| `1511_9` | unused non-ghost `B` | made ghost |
| `307_14` | non-ghost `t`, `B`, two temporaries | ghost; source's call restored |
| `1043_358` | append routed through `oldLines`, `piece` | source's appends restored |

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
were later proved by the main agent with the prelude lemmas, outside the budget.
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
the Python recursion support the rerun. The rerun proof replaced the overlay
proof on 2026-09-24.

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

The current files are the single source of truth. Superseded data is in the
`old-` files.

| file | contents |
|---|---|
| `manifest.jsonl`, `excluded.jsonl` | the draw |
| `slice_{a,c2,ra,rb,rc}.jsonl`, `PROMPT_{a,c2,rerun}.md` | slices and briefs of the records kept |
| `traj_{a,c2,ra,rb,rc}.jsonl` | one record per row, 50 in all |
| `label_relation.jsonl` | reviewed relation for each proved original-run row, and for `1718_1166`, whose proof predates the rerun; rerun records carry their own |
| `audit.jsonl`, `summary.json` | verifier results joined to records |
| `old-record.jsonl` | every superseded line, as `{file, superseded_on, why, record}`: the original B and C records, the rerun's staging records and verifier results, and earlier revisions |
| `old-slice_{b,c}.jsonl`, `old-PROMPT_{b,c}.md` | the original run's slices B and C and their briefs |

`PROMPT_rerun.md` names paths under `rerun/`, where the rerun worked. That
directory was folded into this one on 2026-09-29.
