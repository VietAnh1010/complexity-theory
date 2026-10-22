# `solutions-disputed/`: label problems to review

Rows whose label does not match what the code costs. **A queue for human
review; nothing here is decided.** Each file's header gives the class the audit
thinks is right (`true_class`), the cause, the confidence and the evidence.

Rows got here through `label_audit.py apply`, from verdict files that passed
`label_audit.py check`. They stay in the dataset, and the test gates still run
on them; `verify_all.py` does not (`DOCS.md` § The gates). Some also have a
proof in `solutions-proved/`; compare it with the verdict by hand, as no tool
does.

## Verdicts

From `batches/labelaudit/verdicts_r3.jsonl` and `verdicts_r4.jsonl`
(`batches/README.md` describes the rounds). Counts by round, cause and
confidence are in `STATUS.md`.

These verdicts charge `IntToString` 1; the model charges `Digits(x)`
(`COMPLEXITY.md`). Re-check a verdict that depends on that charge where the
text is never printed (a digit sum, a comparison).

| Cause | Meaning | Fix |
|---|---|---|
| `label` | the **Python** isn't the labelled class either | fix the label |
| `translation` | the Python matches; the **Dafny** doesn't | fix the translation |
| `both` | neither matches | both |
| `harness` | both are right: the Python's cost includes parsing stdin, while the Dafny's `Solve` receives input already parsed | document it |

Class `other` means the cost is outside the eleven label classes (`DOCS.md`);
the evidence names it.

`true_class` has held up against every proof in `solutions-proved/`.
**`cause` is less reliable**: review has overturned it both ways (`685_583`,
`396_361`).

## A Dafny that is too fast is a defect

`cause: translation` covers both directions. When the audited class is
**better** than the label, the translation swapped in a faster algorithm
(`CLAUDE.md` § Keep the algorithm). The tests miss it, since the output is
right. Example: `1368_67`'s Python sorts and compares; its Dafny does one
scan. Such rows: `1336_340`, `1366_102`, `1368_67`, `1470_325`,
`1470_470`, `1981_62`, `2087_50`, `2394_182`, `2680_221`, `641_25`, `647_11`,
`669_107`, `894_85`.

- **Too fast:** restore the Python's algorithm; keep the label.
- **Too slow:** change the data structure; keep the algorithm.
- A sequence update is never a defect: it costs 1 (`COMPLEXITY.md`).

## Common patterns

- **A size that cannot vary:** a `requires` fixes the width (`2012_399`), or
  the code reads fixed positions (`171_82`, `89_463`, `525_273`, `396_361`).
- **A constant loop bound:** `531_3456`, `531_3499` (`while i < 5`), `514_39`
  (31). Labelled `O(n)` or worse; really O(1).
- **A step dropped or added:** `685_583`'s Dafny scans where its Python sorts;
  `348_21` imitates a `set` with a linear scan.
- **A value the label leaves out:** `2607_90` loops over `hi - lo`. Fix the
  label, not the code.
- **A size the label doesn't name:** `O(n)` over several strings, or `O(n**2)`
  for two sizes; both are `O(n*m)`.

## `1950_45` and `1950_47`: here for the code

These two are here because their translations fail tests, whatever their
label verdict (`ok` and `mismatch`). Their file header is a
`TRANSLATION AUDIT`, not a label verdict.

- The problem has 42 stored tests. 19 of them fail even for the original
  Python: the `Input` dataclass reads a 100-digit number as a `float`.
- The other 23 can pass. `1950_45` passes 7 of them, `1950_47` passes 19: both
  cut the fraction at 12 digits, where the Python uses `Decimal`.
- Once a row passes all 23, its only failures are the test data's fault, so it
  moves to `solutions-ungateable/` (`batches/gate-audit/` has the evidence).
