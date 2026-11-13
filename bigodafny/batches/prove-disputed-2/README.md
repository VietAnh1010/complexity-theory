# `prove-disputed-2`

Batch 6 of piece C4 in `batches/clean-636/README.md`, the second drawn from
`solutions-disputed/`: 20 of its 166 unproved, gate-passing rows
(`sample.py --dir solutions-disputed`, seed `20261113`, no `--exclude-drawn`). The seed repeats
`prove-disputed-1`'s; the pool had lost that batch's 20 proved rows, so the draw differs. Three
Sonnet agents, 3 attempts and 5 minutes per row. Each brief is `PROMPT.md` followed by
`PROMPT_disputed.md`: prove the tightest upper bound you can.

This is not a measurement of label-proving and stays out of `prove_stats.py`.

**Result: 20 proved, 0 unresolved.**

`excluded.jsonl` holds `1950_45` and `1950_47`: no test gate (B7).

## Relations to the stated label

| relation | rows |
|---|---:|
| `tighter-label` | 10 |
| `tighter-translation` | 4 |
| `looser-structural` | 4 |
| `looser-translation` | 1 |
| `confirms` | 1 |

`label_relation.jsonl` keeps the agents' relations (`review: bound-only`); the main agent did not
re-read each Python.

## Rows whose proof cannot become `truth`

The Dafny does different work from the Python, so the proof bounds another program. Under the
plan's rule these get their translation fixed, not their label changed:

| row | label | proved | what differs |
|---|---|---|---|
| `1437_223` | `O(nlogn)` | `O(n)` | the Python's `valores.sort()` and scan; the Dafny tests `1 in a_list` |
| `799_94` | `O(n**2)` | `O(n)` | the Python's list `in` and `remove`; the Dafny keeps a map of counts |
| `949_67` | `O(n**2)` | `O(n)` | the Python's `cur in vis` on a list; the Dafny uses a set |
| `1231_51` | `O(n*m)` | `O(n)` | `Solve` receives `a_list` parsed and reads only `l[0..2]`; the `m` term is parsing |
| `138_360` | `O(n)` | `O(nlogn)` | the Python counts with a dict; the Dafny sorts |

## Value-bounded

`342_149` is `looser-structural`: its inner loop runs to `x // 2` for each input value `x`. Its
proof moved to `solutions-proved/value-bounded/` with the include fixed and re-verified.

## Fixed by the main agent before promotion

Six proofs compiled to Python other than their row's. All six now match it and re-verify; their
last agent attempt stays under `attempts/`.

- `1047_641`, `1092_11`, `698_155`: a non-ghost temporary became `ghost var`; the row's
  original expression went back into the compiled assignment.
- `1437_223`, `225_145`: the proof turned the row's `if`-expression into a temporary; the
  temporary is now ghost and the expression is back.
- `1357_271`: the proof dropped the row's bare `{ ... }` block around `Solve`'s body; the block
  is back.

## Effort

| attempts used | rows |
|---|---:|
| 1 | 13 |
| 2 | 5 |
| 3 | 2 |

Slice `b` recorded no `seconds` for its 7 rows.
