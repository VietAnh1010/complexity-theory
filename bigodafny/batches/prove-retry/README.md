# `prove-retry`

A retry of the 39 open rows that `obstacle-review/` sorted. It is not a sample: rows were chosen
because they were open. Three Sonnet agents worked the slices.

**Result: 33 proved, 6 unresolved.** The 33 proofs were then all re-proved on `annotate`'s charges,
because agents' hand-written charges proved too low. `traj_*.jsonl` keeps what the agents reported;
`traj.jsonl` has one dated line per row with its current state.

## Why the proofs were redone

`annotate`'s step count, run with each proof's counter on the stored tests, showed two problems:

- The ratio of `annotate`'s count to the proof's counter rose with input size: `514_90`, `1306_126`,
  `2282_16`.
- `annotate`'s count exceeded the proved bound:

| Row | Highest count / bound | Tests over the bound |
|---|---:|---:|
| `514_90` | 5.83 | 181 of 184 |
| `2914_3` | 2.28 | 106 of 145 |
| `2036_33` | 1.31 | 52 of 108 |
| `1626_179` | 1.16 | 38 of 118 |
| `2854_30` | 1.09 | 93 of 94 |
| `2065_24` | 1.02 | 18 of 161 |
| `2005_187` | 1.00 | 2 of 211 |

`2087_119` passed its stored tests and broke its bound by 1.07 on fuzz inputs. So a clean run on
stored tests clears no proof.

## How they were redone

Each proof starts from `annotate`'s output for the row and keeps every charge line. It adds only proof
text. The main agent wrote 11 proofs. Sonnet subagents wrote 22, and the main agent checked them. Each
accepted proof verifies under `dafny verify --verification-time-limit 30`, and its compiled `module_.py`
is byte-identical to the row's.

The one-off check compared annotate's non-comment lines with the attempt's, verified the attempt, then
compared compiled Python before copying it to `solutions-proved/`. It was not kept.

Exceptions to keeping annotate's text exactly:

- `decreases *` is replaced by a real measure, because a proof may not use it.
- `1944_50`: `return x, steps` compiles differently from the row, so it became `r := x; return;`.
- `1332_16`: annotate prints the row's hex limit in decimal, so the proof restores the hex.

`2819_926` keeps a lemma split off from `SqSumLe`, which hit the time limit under load.

## Rows changed

`271_58` and `514_90` called their own quadratic-charged helpers. Both now call the prelude's `Repeat`,
which annotate charges linearly. `271_58` then proves `n + 19`, which confirms its label. `514_90` drops
one power but still carries the bit length of `total_score`. `2819_926` has the same pattern and is
unchanged.

## Relations

`label_relation.jsonl` has one line per proved row. The main agent read each row's Python; the user
reviewed every relation that differed from the agent's.

| Relation | Rows |
|---|---:|
| `looser-structural` | 14 |
| `confirms` | 10 |
| `looser-translation` | 6 |
| `tighter-label` | 2 |
| `looser-slack` | 1 |

Filed in `solutions-proved/value-bounded/`: `281_12`, `342_86`, `514_90`, `1263_2538`, `1626_179`,
`1861_16`, `1871_156`.

Not filed, though the bound carries a value:

- `577_509`, `1944_50`, `2358_103`, `2819_926`: the value term comes from the Dafny or a loose proof,
  not from what the Python pays.
- `1364_161`, `696_51`: the label already counts that value.

## `1306_126`

The proof gives `O(n³)` against label `O(n)`. Fuzzing `annotate`'s count at `n = 1`, steps per `m` stay
near 31 on `all_same` and rise on `half_heavy` (200, 387, 643, 1668 at `m` = 25, 50, 100, 200). The
Python's own `sum` loop also grows: 26 items per `m` at `m = 100`, 251 at `m = 1000`. The statement caps
`m` at 100, so larger sizes show growth only. None of this proves a lower bound.

## Unresolved

| Row | Obstacle | Blocked by |
|---|---|---|
| `457_38` | `math-too-hard` | bounding the iteration count needs a `9^i` against `10^k` comparison |
| `1675_29` | `other` | no counting potential for the iteration count |
| `1972_295` | `other` | needs `a`, `b`, `c >= 1`, which the row does not state |
| `2465_212` | `invariant-gap` | a digit-sum invariant in the output loop |
| `2831_61` | `invariant-gap` | the invariant lacks its empty-sequence fact |
| `2847_21` | `termination-not-proved` | no closed-form position for the spiral walk |

## Open

- **`annotate` charges.** `else if` conditions get none. `s3 == s` on sequences costs 1, and
  `COMPLEXITY.md` has no rule for it. `var f := d`, which translates `d.copy()`, gets none. The prelude's
  `Repeat` is charged linearly by a hardcoded rule, though it recurses like the row-local helpers charged
  quadratically. The accepted proofs inherit all of these.
- **`2231_77`.** The statement says lowercase Latin letters and the row states no such limit. Adding it
  should give `O(n)`; this was not tried.
- **Identical attempts.** Each accepted proof also exists as an attempt that differs only in its
  `include`. `CLAUDE.md` says to delete those, and this batch's brief said to keep them. They are kept
  until that is decided.
- **Agent-proved rate.** `data/prove_stats.md` counts a row as proved by a bounded agent from `outcome` in
  `traj_*.jsonl`. That means the agent's proof verified, not that its charges were right: these 33 count
  though every proof was replaced, and older campaigns' hand-written charges were never compared with
  `annotate`.
- **`audit.py`.** It flags `solutions/271/271_58.dfy` whenever that row has uncommitted changes.
