# `prove-disputed-4`

Batch 8 of piece C4 in `batches/clean-636/README.md`, the fourth drawn from
`solutions-disputed/`: 20 of its 127 unproved, gate-passing rows
(`sample.py --dir solutions-disputed`, seed `20261113`, no `--exclude-drawn`). Three Sonnet
agents, 3 attempts and 5 minutes per row. Each brief is `PROMPT.md` followed by
`PROMPT_disputed.md`: prove the tightest upper bound you can. Each agent's spawn message also
repeated the brief's rule that a proof adds only ghost code.

This is not a measurement of label-proving and stays out of `prove_stats.py`.

**Result: 19 proved, 1 unresolved.**

`excluded.jsonl` holds `1950_45` and `1950_47`: no test gate (B7).

## Relations to the stated label

| relation | rows |
|---|---:|
| `tighter-label` | 8 |
| `looser-structural` | 6 |
| `tighter-translation` | 2 |
| `confirms` | 2 |
| `tighter-costmodel` | 1 |

`label_relation.jsonl` keeps the agents' relations (`review: bound-only`) except `2830_421`: the
agent wrote `tighter-translation`, but its own reason and the label audit say the Python is
linear too, so the main agent recorded `tighter-label` (agent's reason kept as `prover_reason`).

## Rows whose proof cannot become `truth`

| row | label | proved | why |
|---|---|---|---|
| `1913_104` | `O(nlogn)` | `O(n)` | the Python computes an unused `sorted(s)`; the Dafny omits it |
| `1413_222` | `O(n**2)` | `O(n)` | the Python rebuilds `set(x)` inside the loop; the Dafny fills a boolean seq once |
| `2087_50` | `O(n**2)` | `O(n)` | the Python's `a = a[1:]` copies each step; the charge table costs a slice as 1 |

The first two get their translation fixed. `2087_50` is the cost model's view, not the Python's.

## Unresolved

`1276_62` (`O(n+m)`), drawn again after failing in `prove-disputed-3`: `Solve` timed out at
30-60 s on its array loops with `n/i` invariants and the `k-1` outer loop; the agent did not
isolate the cause. It left `obstacle` null; the main agent coded it `z3-nonlinear`, as in
`prove-disputed-3` (`agent_said_obstacle: null`).

## Value-bounded

`1015_129` (builds 2n numbers for an input value n), `1234_71` (trial division to the square root
of each value), `2892_914` (loops over every value in `[a, b]`) and `681_52` (factorial loop up
to the value) are `looser-structural` with a reason naming an input value. Their proofs moved to
`solutions-proved/value-bounded/` with the include fixed and re-verified.

## Agent slip

Slice `a`'s agent skipped `1234_71` (no attempt, no record) and reported 7 proved. `audit.py`
caught the missing record; the same agent was resumed for that row alone and proved it in one
attempt.

## Fixed by the main agent before promotion

`1234_71` (the resumed row) hoisted the row's output line into a non-ghost temporary. It is now
`ghost var line` and the row's expression is back; it re-verifies, and its agent attempt stays
under `attempts/`. `1015_129`'s agent changed "assumes" to "presumes" in a header comment after
saving its attempt, so that attempt differs from the proof by one comment word and is kept.

## Effort

| attempts used | rows |
|---|---:|
| 1 | 15 |
| 2 | 2 |
| 3 | 3 |
