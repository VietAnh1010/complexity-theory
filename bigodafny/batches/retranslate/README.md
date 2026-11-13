# retranslate (2026-11-12)

Stage B4 of the clean-636 plan: rows whose Dafny does not follow the Python's algorithm. 38 rows: 31
disputed rows with audit cause `translation` or `both`, minus the 9 that hinge on a square root
(handled separately), plus 8 rows the `verify-clean` agents reported. Four slices,
one general-purpose agent each, brief
`PROMPT.md`.

## Audit (parent, from scratch)

Every changed row: `dafny verify` ends `N verified, 0 errors`; no `assume` or `decreases *` in
code; `validate.py --only` (strict) or `difftest.py --only` (loose) passes. No `requires` added.

## Changed (31)

`348_21`, `669_107`, `894_85`, `1336_340`, `3029_114`, `565_158`, `685_583`, `1027_141`,
`1366_102`, `1470_470`, `1853_137`, `1981_62`, `2193_70`, `3029_74`, `641_25`, `1027_458`,
`1368_67`, `1671_196`, `1853_66`, `1997_311`, `2217_419`, `2853_327`, `647_11`, `700_99`,
`1180_39`, `1434_1729`, `1742_66`, `1861_28`, `2005_137`, `2394_182`, `2947_125`.

Each now uses the Python's structure: `Sort` where it sorts, `map` for a dict or `Counter`, `set`
for a set, a binary heap for `heapq`, a binary search for `bisect`, a slice sum per step for
`sum(X[i:n])`. `647_11` and `685_583` have proofs of the old code; `proofs.py` flags them until
they are re-proved.

## Unchanged (7)

- `1470_325`, `2087_50`, `2516_236`, `2680_221`: the Python copies a list (`del l[0]`, `a[1:]`,
  slice rebuilds, `pop(0)`); the model charges the Dafny's view or update 1 (`COMPLEXITY.md`).
- `1827_44`: the loops match the Python's; `Pow2` recursion is how the model charges `2 ** x`.
- `1950_47`: the Python is `Decimal` library calls only; the Dafny does the scaling `Decimal` does.
- `700_233`: the Python itself uses the closed form; the verify-clean note was wrong.
