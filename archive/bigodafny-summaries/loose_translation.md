# Translating the loose rows

The last 104 untranslated rows: 100 `loose`, 4 `unvalidatable`.

**100 of 104 translated. 95 of 101 audited rows agree with their own Python.**

## Why they needed a different gate

`validate.py` compares against BigOBench's stored output. These problems accept
more than one correct answer, so the stored output is one of several and even
the original Python fails a byte-diff against it.

`difftest.py` runs the row's own Python and its Dafny on the same inputs and
compares them to each other. That is the real question for a transpilation
dataset, and it stays decidable where the stored output does not.

The instruction that follows from it: **be literal**. Reproduce the Python's
arbitrary choices — which valid answer it prints, what order, which index it
lands on — and reproduce its bugs. A tidier answer is a failure.

## Result

    agrees   95
    differs   5

All 5 differing rows are exactly the `unvalidatable` split: `1196_100`,
`1578_481`, `1578_724` (their `from_str` raises on some stored inputs) and
`1950_45`, `1950_47` (a `real` argument whose ~100-digit decimals are destroyed
by Python `float()` before Dafny is called). Harness limits, not translation
errors.

## The 4 left untranslated

`967_19`, `967_5`, `3079_181`, `3079_85` all `print()` a raw Python float.
Matching that byte-for-byte needs bit-exact IEEE-754 arithmetic plus CPython's
shortest-round-trip repr; Dafny's `real` is an exact rational and diverges.

Tractable with a format spec, not without one: `2496_30` computes in exact
rationals and hand-writes `FormatG9` to replicate `'{:.9}'.format(x)`, agreeing
on all 42 comparable tests.

## Fourth dataclass mismatch

`2771_23`/`2771_26`: BigOBench's dataclass carries a `[0]`-prefix for this
problem and no other. One Python indexes 0-based, the other re-prepends `[0]`
itself, so one translation must strip the prefix and the other must not. Both
failed difftest until the agent read the dataclass.

## Two tooling fixes this forced

`difftest` emitted results only after the last row, so a kill lost the run. It
now appends each result as it lands and resumes from the partial file.

It also used `ex.map`, which yields in order — one slow row blocked every
completed row behind it. `as_completed` took the same work from 18 rows in 25
minutes to 98 in 3.
