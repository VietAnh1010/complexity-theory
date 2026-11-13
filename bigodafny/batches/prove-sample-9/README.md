# `prove-sample-9`

Campaign 1 of 9 to prove every unproved row. Label audit r5 (`batches/labelaudit/verdicts_r5.jsonl`)
moved 71 rows into `solutions/`, so the never-drawn pool held 80 rows again. This campaign draws 20
of them (`--exclude-drawn`, seed `20261113`). The other 60 go to later batches. Three Sonnet agents,
3 attempts and 5 minutes per row, the default brief.

**Result: 20 proved, 0 unresolved.** Every row has a `reads` trace. `audit.py` reports no
disagreement between the trajectories and the verifier.

`excluded.jsonl` holds 1 row, `1972_295`, drawn by an earlier campaign. It still has no proof.

## Slices

| slice | rows | proved |
|---|---:|---:|
| `traj_a` | 7 | 7 |
| `traj_b` | 7 | 7 |
| `traj_c` | 6 | 6 |

## Rates by label

| label | proved |
|---|---:|
| `O(n)` | 11 / 11 |
| `O(nlogn)` | 5 / 5 |
| `O(1)` | 1 / 1 |
| `O(n**2)` | 1 / 1 |
| `O(n*m)` | 1 / 1 |
| `O(nlogn+mlogm)` | 1 / 1 |

Use the pooled figures in `data/prove_stats.md`, not this campaign alone.

## Relations

19 proofs confirm their labels. One does not:

| row | label | proved | relation | why |
|---|---|---|---|---|
| `294_56` | `O(n**2)` | cubic | `looser-slack` | the statement fixes `s` to lowercase letters, so the loop over `set(s)` runs at most 26 times; the row lacks that `requires`, so the proof bounds it by `\|s\|` |

The agent wrote `looser-structural` for `294_56`; `label_relation.jsonl` keeps that as
`prover_relation`. The row needs the lowercase `requires` (its statement's limit) and a proof
that bounds the distinct letters by 26. That needs a hand proof. `294_56` also took 420 seconds against
the 5-minute limit; 19 rows closed within budget.

`2089_8` and `482_543` loop over input values; their labels count those values as sizes, so both
confirm. `952_116` charges its own `ReverseInts` as `3 * |arr| + 1`, which `COMPLEXITY.md`
allows for a helper that recurses once per element.

## Fixed by the main agent before promotion

`audit.py` found 2 proofs whose emitted Python differed from their row's:

- `2089_8`: a proof-only `var mb` became `ghost var mb`.
- `2627_568`: a non-ghost `var t := IntToString(...)` was inlined back into the row's
  expression, and the step update reads `lines[i - 1]`.

Both re-verify.

## Effort

| attempts used | rows |
|---|---:|
| 1 | 14 |
| 2 | 4 |
| 3 | 2 |
