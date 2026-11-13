# `prove-sample-12`

Campaign 4 of 9 to prove every unproved row. Takes all 20 never-drawn, unproved rows left in
`solutions/` (`--exclude-drawn`, seed `20261113`), so it is a census of the remainder, not a sample.
Three Sonnet agents, 3 attempts and 5 minutes per row, the brief and the `ghost` line of
`prove-sample-10`.

**Result: 20 proved, 0 unresolved.** Every row has a `reads` trace. Every row closed within its
time budget.

`excluded.jsonl` holds 2 rows drawn by earlier campaigns: `1972_295` and `2282_1118`. Neither
has a proof.

## Slices

| slice | rows | proved |
|---|---:|---:|
| `traj_a` | 7 | 7 |
| `traj_b` | 7 | 7 |
| `traj_c` | 6 | 6 |

## Rates by label

| label | proved |
|---|---:|
| `O(n)` | 13 / 13 |
| `O(n**2)` | 4 / 4 |
| `O(nlogn)` | 3 / 3 |

Use the pooled figures in `data/prove_stats.md`, not this campaign alone.

## Relations

19 proofs confirm their labels. One does not:

| row | label | proved | relation | why |
|---|---|---|---|---|
| `1467_233` | `O(n)` | `O(N log N)` | `looser-structural` | the Python builds `str(i)` for every `i < N + 100`; the digits sum to `Theta(N log N)`, and only `t[N]` reaches the output |

The main agent re-read the Python: `t += str(i)` builds the whole string, so the cost is the Python's,
not the translation's. `1467_233` passed label audit r5 as `ok`; its `truth` is not settled.

## Fixed by the main agent before promotion

`225_85`, `3005_182` and `397_80` declared non-ghost temporaries (`res`, `line`), so their emitted
Python differed from their rows'. Each became a `ghost var`, and the row's original expression went
back into the compiled assignment. All three re-verify.

## Effort

| attempts used | rows |
|---|---:|
| 1 | 14 |
| 2 | 5 |
| 3 | 1 |
