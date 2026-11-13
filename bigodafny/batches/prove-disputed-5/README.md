# `prove-disputed-5`

Batch 9 of piece C4 in `batches/clean-636/README.md`, the fifth drawn from
`solutions-disputed/`: 20 of its 108 unproved, gate-passing rows
(`sample.py --dir solutions-disputed`, seed `20261113`, no `--exclude-drawn`; no row had been
drawn before). Three Sonnet agents, 3 attempts and 5 minutes per row. Each brief is `PROMPT.md`
followed by `PROMPT_disputed.md`: prove the tightest upper bound you can. Each agent's spawn
message also repeated the brief's rule that a proof adds only ghost code.

This is not a measurement of label-proving and stays out of `prove_stats.py`.

**Result: 16 proved, 4 unresolved.**

`excluded.jsonl` holds `1950_45` and `1950_47`: no test gate (B7).

| label | drawn | proved |
|---|---:|---:|
| `O(n)` | 4 | 2 |
| `O(n**2)` | 8 | 6 |
| `O(n*m)` | 3 | 3 |
| `O(nlogn)` | 5 | 5 |

## Relations to the stated label

| relation | rows |
|---|---:|
| `looser-structural` | 7 |
| `tighter-label` | 4 |
| `confirms` | 2 |
| `tighter-translation` | 2 |
| `looser-costmodel` | 1 |

The main agent re-read the Python for every row below its label (`review: read-python`) and
changed two relations (agent's reason kept as `prover_reason`):

- `1548_179`: agent wrote `tighter-translation` (per-line parse not charged). Each query line
  holds exactly three ints, so the Python is linear too: `tighter-label`.
- `1722_66`: agent wrote `tighter-label`. The bound is linear in the total cube-list length,
  6 faces per cube, so it is in the label's `O(n)`: `confirms`. `O(1)` would need the six-face
  limit as a `requires`.

`2723_27` confirms only if the label's `m` is the largest `a_i`; the row does not say.

## Rows whose proof cannot become `truth`

| row | label | proved | why |
|---|---|---|---|
| `333_197` | `O(nlogn)` | `O(n)` | the Python sorts the indices and calls `word.pop(r)` per index; the Dafny makes one pass |
| `397_163` | `O(nlogn)` | `O(n)` | the Python takes `sorted(c.values())[0]`; the Dafny finds the max by a scan |

Both get their translation fixed (C6).

## Unresolved

| row | label | obstacle | what blocked it |
|---|---|---|---|
| `531_3456` | `O(n)` | `invariant-gap` | the invariant's constant 60 was below the 67 one iteration needs |
| `2065_128` | `O(n)` | `z3-nonlinear` | `i*K` in the invariant and `(ISqrt+2)*(...)` in the `ensures` timed out at 30 s |
| `960_36` | `O(n**2)` | `invariant-gap` | the outer invariant was not maintained; the failing branch was not isolated |
| `2854_107` | `O(n**2)` | `invariant-gap` | bounding pops by `2E+1` needs "a re-popped visited node pushes nothing" |

No agent set `obstacle`; the main agent coded each from `why_failed` (`agent_said_obstacle: null`).

## Value-bounded

`1263_1960` (digit loop per input value), `1234_634` (trial division to the square root of each
value) and `2892_1216` (loops over every value in `[a, b]`) are `looser-structural` with a reason
naming an input value. Their proofs moved to `solutions-proved/value-bounded/` with the include
fixed and re-verified.

## Agent slips

- Slice c's agent left `2854_107` unresolved with no attempt. Resumed, it made one attempt
  (saved) and stopped. Asked in the same resume, it tied `1722_66`'s `M+4` charge per list scan to the
  real list lengths with asserts (attempt 2).
- Slice a's agent did not save `531_3456`'s first attempt ("resolution error"). `audit.py`
  reports 3 attempts recorded and 2 kept; the file is lost.
- `seconds` is null for slice b's 7 rows: that agent did not time them.

## Fixed by the main agent before promotion

`1234_634` and `1369_10` hoisted the row's output expression into a non-ghost temporary. Each
temporary is now `ghost var` and the row's expression is back. `1234_634` then timed out until
an `assert` equating the two appended seqs was added; both re-verify. Their agent attempts stay
under `attempts/`.

## Charged by formula

`1338_61` calls three row functions (`ReverseSeq`, `FindMinIndex`, `RemoveAt`), which cannot
take a ghost `steps`. It charges each a closed form linear in the seq length (`3n+2`,
`8n+10` for find-and-remove). Each is at least what the charge table gives the function, so the
`O(q*n**2)` bound is an upper bound.

## Effort

| attempts used | rows |
|---|---:|
| 1 | 11 |
| 2 | 5 |
| 3 | 4 |
