# `prove-sample-11`

Campaign 3 of 9 to prove every unproved row. Draws 20 of the 40 never-drawn, unproved rows left in
`solutions/` (`--exclude-drawn`, seed `20261113`). Three Sonnet agents, 3 attempts and 5 minutes per
row, the brief and the `ghost` line of `prove-sample-10`.

**Result: 19 proved, 1 unresolved.** Every row has a `reads` trace.

`excluded.jsonl` holds 1 row, `1972_295`, drawn by an earlier campaign. It still has no proof.

## Slices

| slice | rows | proved |
|---|---:|---:|
| `traj_a` | 7 | 7 |
| `traj_b` | 7 | 6 |
| `traj_c` | 6 | 6 |

## Rates by label

| label | proved |
|---|---:|
| `O(n)` | 8 / 8 |
| `O(n**2)` | 5 / 5 |
| `O(nlogn)` | 4 / 5 |
| `O(1)` | 1 / 1 |
| `O(n**2+m**2)` | 1 / 1 |

Use the pooled figures in `data/prove_stats.md`, not this campaign alone.

## Unresolved

| row | obstacle | why |
|---|---|---|
| `2282_1118` | `math-too-hard` | the lemma summing the `IsMin` charges (`Digits`, `SumDigits` of the sorted list, `SortCost`) timed out at 30 s on all 3 attempts |

The agent also notes that the row's recursive `"9" + rec` string builders cost `|t|` per call,
so even a closed proof would be quadratic against the `O(nlogn)` label. The agent wrote no
`obstacle`; the main agent filled in `math-too-hard` from its `why_failed`. The row took 600
seconds against the 5-minute limit and stays unresolved.

## Relations

All 19 proofs confirm their labels.

## Effort

| attempts used | rows |
|---|---:|
| 1 | 13 |
| 2 | 5 |
| 3 | 2 |
