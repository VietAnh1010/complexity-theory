# Wave 3, batch 4

20 rows, `1138_66` .. `1254_187`. Agent: Sonnet, 105k tokens, 42 tool calls.

| | |
|---|---|
| Agent reported | 18/20 valid, 2 parser-blocked |
| Independent audit | **18/20 valid**, same 2 |
| Reverted | 0 |
| Needed extended timeout | 0 |

## The two failures are not translation bugs

`1196_100` and `1196_51` fail before `Solve` is ever called. BigOBench's own
`Input.from_str` does `*text_list, _ = input_.split('\n')`, assuming a trailing
newline. These tests have none, so it mis-slices and raises `AssertionError`.

The agent's diagnosis was checked, not taken on trust. Scanning all 640 rows,
exactly 4 have a `from_str` that raises on at least one of their own stored
tests: `1196_100`, `1196_51`, `1578_481`, `1578_724`. That reproduces a Step 0
measurement exactly — 18 AssertionErrors, 2+2+7+7.

No translation of these rows can ever pass. Counting them as `fail` measures the
parser, not the code. `dataset.py` now assigns them `split: unvalidatable` and
records `parser_ok` per row. Splits are now strict 536, loose 100,
unvalidatable 4.

## Example worth keeping

`1234_634` — the Python takes `sorted(factors(n))[-2]`. The first translation
read that as "largest `i` with `i*i <= n` and `n % i == 0`", which is wrong. The
value is `n // p` for `p` the *smallest* divisor >= 2, or 1 when `n` is prime.
Fixed, 28/28.

A plausible misreading of a one-line Python idiom, caught only by the tests.
This is the argument for the validator gate in one row.

## Carried forward

String lexicographic ordering was hand-written twice here (`StringLess`).
`ParseInt` is hand-written in 9 files. Both belong in `prelude.dfy`, added
between waves rather than during one, since a compile error there breaks every
running agent at once.
