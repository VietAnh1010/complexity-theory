# `solutions-ungateable/`: no test verdict is possible

Rows not known to be wrong or right. The evidence a gate needs does not
exist: for most, the stored tests are broken; for `1501_224`, the tests that
would settle it time out. Each file's `GATE INAPPLICABLE` header repeats
its entry in `data/gate_ungateable.jsonl`.

## `validate.py` rows: broken tests

| Row | Stored tests | Tests that can run | Dafny passes |
|---|---|---|---|
| `1196/1196_100.dfy` | 12 | 10 | 10 |
| `1196/1196_51.dfy` | 12 | 10 | 10 |
| `1578/1578_481.dfy` | 8 | 1 | 1 |
| `1578/1578_724.dfy` | 8 | 1 | 1 |

Every test that can run, passes. The rest are rejected by the problem's own
`Input.from_str` (`dataset.py` marks these rows `unvalidatable`):

- **1578** asserts every row has `n` columns, but rows always have 3, so every
  test with `n != 3` fails: 7 of 8.
- **1196** has two tests that say `n = 4` and give three lines.

`baseline.py --round-trip` shows the original Python fails in exactly the same
places, so the tests are at fault, not the translation.

## `difftest.py` row: timeouts

`1501_224` (loose): of 122 tests, 29 have no Python result to compare; of the
other 93, **77 agree, 0 disagree, 16 time out**. `difftest.py` needs all
comparable tests to agree, so it reports `differs`. A re-run takes ~39 minutes.

## Getting out

1. **Fixed tests:** if BigOBench corrects them, re-run the gate.
2. **A ruling on timeouts:** `1501_224` needs a decision on whether a timeout
   counts against a row. Still open.

Never loosen a gate to let a row out.
