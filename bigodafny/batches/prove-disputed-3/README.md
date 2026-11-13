# `prove-disputed-3`

Campaign 7 of 9 to prove every unproved row, the third drawn from `solutions-disputed/`: 20 of its
146 unproved, gate-passing rows (`sample.py --dir solutions-disputed`, seed `20261113`, no
`--exclude-drawn`). Three Sonnet agents, 3 attempts and 5 minutes per row. Each brief is `PROMPT.md`
followed by `PROMPT_disputed.md`: prove the tightest upper bound you can. Each agent's spawn message
also repeated the brief's rule that a proof adds only ghost code (`ghost var` for any temporary).

This is not a measurement of label-proving and stays out of `prove_stats.py`.

**Result: 19 proved, 1 unresolved.**

`excluded.jsonl` holds `1950_45` and `1950_47`: no test gate (`unvalidatable`).

## Relations to the stated label

| relation | rows |
|---|---:|
| `tighter-label` | 7 |
| `looser-structural` | 4 |
| `looser-translation` | 3 |
| `confirms` | 3 |
| `looser-slack` | 1 |
| `tighter-translation` | 1 |

`label_relation.jsonl` keeps the agents' relations (`review: bound-only`); the main agent did not
re-read each Python.

## Rows whose proof cannot become `truth`

The Dafny does different work from the Python, so the proof bounds another program. These get
their translation fixed, not their label changed:

| row | label | proved | what differs |
|---|---|---|---|
| `1054_216` | `O(n**2)` | `O(n)` | the Python rescans lists (`not in`, `remove`); the Dafny counts in one map pass |
| `619_340` | `O(nlogn)` | `O(n**2)` | the Python counts with a dict; the Dafny tests membership on a seq |
| `1306_197` | `O(nlogn)` | `O(n**2)` | the Python uses `Counter`; the Dafny regroups by `CountOccur` and `RemoveAll` |
| `1593_264` | `O(n)` | `O(n**2)` | the Python's `Counter` is one pass; the Dafny rescans the string per bigram |

`1640_36` is `looser-slack`: each `gcd` is charged its own Euclid depth, where the running gcd
amortises to `O(n + log V)`. Its proof is sound but too loose to settle `truth`.

## Unresolved

`1276_62` (`O(n+m)`): six loops plus a `rep * K` product and an `ISqrt` invariant timed out at 30 s
on all 3 attempts. The agent left `obstacle` null; the main agent coded it `z3-nonlinear`
(`agent_said_obstacle: null` in the record). Its 3 attempts are under `attempts/1276/`.

## Value-bounded

`2607_25` (loops over coordinate values) and `788_22` (a doubling loop per element, the bit
length of the value) are `looser-structural` with a reason naming an input value. Their proofs
moved to `solutions-proved/value-bounded/` with the include fixed and re-verified.

## Fixed by the main agent before promotion

`2602_57` and `2610_1259` hoisted row expressions into non-ghost temporaries, so their emitted
Python differed from the row's. The temporaries are now `ghost var` and the row's expressions
are back. Both re-verify; their last agent attempt stays under `attempts/`.

## Effort

| attempts used | rows |
|---|---:|
| 1 | 9 |
| 2 | 6 |
| 3 | 5 |
