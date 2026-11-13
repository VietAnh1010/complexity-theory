# `prove-sample-10`

Batch 2 of piece C4 in `batches/clean-636/README.md`. Draws 20 of the 60 never-drawn, unproved
rows left in `solutions/` after `prove-sample-9` (`--exclude-drawn`, seed `20261113`). Three
Sonnet agents, 3 attempts and 5 minutes per row, the default brief. The agent prompt adds one
line: every variable added for the proof must be `ghost`, because two `prove-sample-9` proofs
compiled to different Python by declaring a proof-only temporary without it.

**Result: 20 proved, 0 unresolved.** Every row has a `reads` trace. `audit.py` reports no
disagreement between the trajectories and the verifier. Every row closed within its time budget.

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
| `O(n)` | 14 / 14 |
| `O(nlogn)` | 4 / 4 |
| `O(n**2)` | 1 / 1 |
| `O(1)` | 1 / 1 |

Use the pooled figures in `data/prove_stats.md`, not this campaign alone.

## Relations

18 proofs confirm their labels. Two do not, and one agent claim was overruled:

| row | label | proved | relation | why |
|---|---|---|---|---|
| `1303_8` | `O(n**2)` | constant + `\|output\|` | `tighter-label` | both Python loops are capped by the source literal 55556, so the Python is bounded by a constant |
| `294_131` | `O(n)` | quadratic | `looser-slack` | as `294_56` in `prove-sample-9`: the statement's 26-letter alphabet bounds the loop over `set(s)`; the row lacks that `requires` |
| `966_134` | `O(n)` | linear in input length | `confirms` | the agent wrote `looser-structural` for `ParseInt`'s per-character cost; that cost is linear in the input's length, so the bound is in `O(n)` |

`1303_8` passed label audit r5 as `ok`, but its proof puts it in `O(1)`. Its `truth` is settled in
C3/C6. `294_131` goes to C5 with `294_56`.

## Effort

| attempts used | rows |
|---|---:|
| 1 | 15 |
| 2 | 4 |
| 3 | 1 |
