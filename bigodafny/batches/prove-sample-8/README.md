# `prove-sample-8`

The last fresh-only draw. Only 18 labelled, gate-passing, unproved rows in
`solutions/` had never been drawn, so this campaign takes all of them
(`--exclude-drawn`, seed `20260924`, which fixes only the slice order). It is
a census of the remaining rows, not a sample. Three Sonnet agents, 3 attempts
and 5 minutes per row.

**Result: 16 proved, 2 unresolved.** Every row has a `reads` trace.
`audit.py` reports no disagreement between the trajectories and the verifier.

This is the first campaign whose brief included both the reading trace and the
prelude's sort-cost and binary-search lemmas from the start.

## Slices

| slice | rows | proved |
|---|---:|---:|
| `traj_a` | 6 | 6 |
| `traj_b` | 6 | 6 |
| `traj_c` | 6 | 4 |

## Rates by label

| label | proved |
|---|---:|
| `O(n)` | 9 / 11 |
| `O(n**2)` | 3 / 3 |
| `O(1)` | 2 / 2 |
| `O(nlogn)` | 1 / 1 |
| `O(nlogn+mlogm)` | 1 / 1 |

With 18 rows, one row changes the rate by more than five points. Use the pooled
figures in `data/prove_stats.md`, not this campaign alone.

## Unresolved rows

| row | obstacle | why |
|---|---|---|
| `2087_119` | `invariant-gap` | the inner loop's potential invariant did not hold on the exit branch |
| `2231_77` | `prelude-gap` | bounding a character-keyed map by its 27-symbol alphabet needs a cardinality lemma the prelude lacks |

`2231_77` recorded 420 seconds against the 5-minute limit. It remained
unresolved, so the overrun did not inflate the result.

## Relations

All 16 proofs `confirm` their labels. Every bound is in its label's class, so no
relation needed review.

Both sort rows used the prelude directly. `1718_621` proves
`2*NLogN(|list1|) + 2*NLogN(|list2|) + linear` against `O(nlogn+mlogm)`, and
`3017_45` proves `2*NLogN(n) + 5n + 5` against `O(nlogn)`. Neither defines a
local `SortCost`.

## Effort

| attempts used | rows | proved |
|---|---:|---:|
| 1 | 12 | 12 |
| 2 | 3 | 3 |
| 3 | 3 | 1 |

Median time was 90 seconds per row.

The 18 traces contain 55 entries: 22 source reads, 32 prelude reads, and 1
helper read. The median trace has 3 entries; the longest has 6. The most
frequently read prelude declarations were `IntToString` and `Join`.

## Files

| file | contents |
|---|---|
| `manifest.jsonl`, `excluded.jsonl` | the draw |
| `slice_{a,b,c}.jsonl`, `PROMPT_{a,b,c}.md` | slices and prompts |
| `traj_{a,b,c}.jsonl` | one record per row |
| `obstacles.jsonl` | obstacle codes for the 2 unresolved rows |
| `label_relation.jsonl` | empty: no relation needed review |
| `audit.jsonl`, `summary.json` | verifier results joined to records |
