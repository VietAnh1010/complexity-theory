# Verification wave 3

Ran `dafny verify` to ground on everything left in `solutions-unverified/`.

**`solutions/` 338 -> 488. `solutions-unverified/` 171 -> 21.**

| batch | who | verify |
|---|---|---|
| verify2 w_01..w_04 | agents | 78 / 80 |
| verify3 w_00 | agent | 9 / 16 |
| verify3 w_01 | agent | 15 / 16 |
| verify3 w_02 | agent | 14 / 16 |
| verify3 w_03 | agent | 16 / 16 |
| verify3 w_04, w_05 | by hand | 27 / 27 |

Every batch re-verified, re-validated and re-prechecked from scratch. Zero
`assume` anywhere. Four `decreases *`, each with its reason in the file.

## The gate was not gating

`precheck.py` evaluates each added `requires` against every stored input. It
had four bugs, and together they let 29 of 444 clauses pass without ever being
evaluated:

- a `//` comment between two `requires` was appended to the previous clause
- `'A' <= s[t] <= 'Z'` became `'I.A' <= I.s[t] <= 'I.Z'` -- valid Python,
  always false, reported VIOLATED. A wrong answer, not a missing one.
- `no-data` (translated, then raised on every input) was recorded and never
  printed
- `exists`, element quantifiers, arbitrary numeric ranges, implication and the
  prelude helpers all fell through to `unchecked`

Fixed: 430 of 434 clauses now evaluate, 0 violated, 4 genuinely untranslatable.

Six preconditions were violated on real data and are gone. `1332_41`'s
`exists c :: a_list[c] == k` failed on a **private** test -- a tier
`validate.py` gates on, so that proof did not cover the data the row is scored
against. Three rows have now tried to assume the answer exists.

## Sort keeps its elements

`Sort` carried only a length postcondition, so every fact about a sequence's
contents died at the sort. Added and proved in the prelude:
`MergeIsPermutation`, `SortIsPermutation`, `SortKeepsElems`,
`SortIntsKeepsElems`, `SortStringsKeepsElems`. State the fact in **membership**
form, not indexed form, and the lemma applies directly.

## Two counting mistakes of my own

`grep -q "0 errors"` also matches "10 errors". Every sweep was re-run against
`verifier finished with \d+ verified, 0 errors`. No false pass reached a clean
directory; one reached a commit message (1369_10, corrected in 867a361).

`dafny verify` caps output at 5 errors. Use `--error-limit 0` while diagnosing.

## What is left

17 rows do not verify, each for a stated reason:

- **the data is out of spec** (7): `1981_39` indexes `b[a_list[i] - 1]`, safe
  only if every value is in `1..n`; 91 of 103 inputs break that. The
  translation is genuinely unsafe on the data it ships with.
- **safety is existential** (4): the guarantee is "a solution exists", which is
  not a precondition we accept.
- **needs a non-local argument** (5): prefix sums over a sliding window
  (`888_179`, `888_6`), fuel accumulation (`2019_311`).
- **Z3 cannot close it** (1): `1336_157`'s bv64-to-int comparison times out in
  isolation.

Four more verify but fail their behavioural gate and are held out of
`solutions/`: `1196_51`, `1950_45`, `1950_47` differ from their own Python;
`1738_180` fails 1 of 32 tests. All predate this pass.

## Worth keeping

`1827_66` had two preconditions rejected (`b >= 1`, then `b >= 0`) before the
real answer turned out to be that it needs none: when `b < 1` the loops simply
do not run, and two guarded invariants say so. The first instinct on an
unconstrained `int` is to constrain it.
