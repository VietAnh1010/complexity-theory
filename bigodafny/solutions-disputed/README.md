# `solutions-disputed/` — label audit review queue

202 rows whose stated complexity label does not describe what the code costs.
**Queued for manual review; nothing here is a decision.** Each file keeps its
full original body with a header naming the audited class, the cause, the
confidence and the evidence, so a reviewer needs nothing else open.

Produced by `label_audit.py` from agent verdicts that passed `checkverdicts.py`,
with every mismatch re-checked by the orchestrating session before the move.
History: `../CHANGELOG.md`.

## These rows are still in the dataset

Quarantined, not removed. `solutions-disputed` is in the root list of
`validate.py`, `difftest.py`, `precheck.py` and `proofs.py`; the rows keep
their labels and appear in `data/dataset.jsonl`. 44 of them also carry a
machine-checked proof in `solutions-proved/`, the strongest input a reviewer
can have; `checkverdicts.py` rejects any verdict that contradicts one.

## Where the verdicts come from

| rows | verdict source | rules it applied |
|---|---|---|
| 45 | re-audit r3, `batches/labelaudit/verdicts_r3_*.jsonl` | input values are cost parameters; `IntToString` costs 1; `Gcd` costs Euclid's depth |
| 152 | the first audit, after the cost-model re-file | stipulated collection costs; a capped value is a constant |
| 5 | no `mismatch` verdict | `810_131`, `1484_26`, `2607_90` (value-versus-size convention); `1950_45`, `1950_47` (translation audit) |

Two rules have changed since some verdicts were made:

- **Values.** `COMPLEXITY.md` counts a loop bounded by an input value. The
  first audit treated a capped value as a constant, so its value-loop verdicts
  may invert. See "Open questions".
- **Output.** `IntToString(x)` now costs `Digits(x)`, and an additive
  `|output|` term never counts against a label. A verdict that relies on
  `IntToString` costing 1 where the string is not output (a digit sum, a
  comparison) may need re-checking.

## Counts

| cause | rows | what is wrong | repair |
|---|---:|---|---|
| `label` | 155 | the **Python** is not the labelled class either | fix the label |
| `translation` | 39 | the Python matches its label; the **Dafny** does not | fix the translation |
| `both` | 6 | neither matches | both |
| `harness` | 2 | both are right; the dataset drew the boundary differently | document it |

Confidence: 120 high, 74 medium, 6 low; the two translation-audit rows carry
none. 53 rows have `audited class: other`: the true cost is outside the
eleven-class vocabulary (cubic, or a cost in a value), named in the evidence.

`harness` is the subtle one. The Python reads stdin and pays to parse every
input, and BigOBench profiled the whole script. The Dafny's `Solve` takes those
inputs already parsed. A Python that does `b = list(map(int, input().split()))`
and then reads only `b[0]` is genuinely O(n+m) while its faithful Dafny is
O(n). Nothing is wrong with either.

## A `translation` row can be too FAST, and that is the worse defect

Both directions land as `cause: translation`, and they need opposite repairs.
`translation_defect: true` marks only the Dafny being *slower*; the other
direction is `cause: translation` with the audited class **better** than the
label.

    label O(nlogn) -> audited O(n)   the Dafny is faster than the Python

That is not a win. `bigodafny/CLAUDE.md` § "Preserve the algorithm" forbids it,
and both gates miss it: the output is right. Comparing header classes finds 12
such rows: `1336_340`, `1366_102`, `1368_67`, `1470_325`, `1470_470`,
`1981_62`, `2087_50`, `2394_182`, `641_25`, `647_11`, `669_107`, `894_85`.
Confirmed by reading both sources:

| row | what the Python does | what the Dafny does |
|---|---|---|
| `1368_67` | `t = sorted(s)`, then `s != t` | one adjacent-pair scan, no `Sort` call |
| `1470_470` | `ar = sorted(ar)` | two linear scans with early break |
| `1470_325` | `del l[0]` in a loop — the real O(n**2) | a two-pointer `lo`/`hi` scan |
| `685_583` | `sorted(a)` then `a[-1]` | two linear maxima |

**Repair: restore the Python's algorithm, do not change the label.** The label
is correct about the program BigOBench measured; relabelling to match a faster
translation bakes the defect in. The ordinary direction, audited class *worse*
than the label, is repaired the opposite way: change the data structure, keep
the algorithm.

A `seq` update is never a translation defect: `COMPLEXITY.md` § 1 charges
`s[i := v]` 1, so a row whose only difference is a copying collection is `ok`.
Do not rewrite it or reach for another container.

## Recurring shapes

- **A dimension that cannot vary.** `O(n*m)` where a `requires` pins row width
  (`276_1206`) or the body reads only fixed positions (`171_82`, `89_463`,
  `525_273`, `396_361`).
- **A loop bounded by a literal constant.** `531_3456` and `531_3499` loop
  `while i < 5`; `514_39` is bounded by 31. Labelled `O(n)` or worse, truly O(1).
- **A dropped or added algorithm step.** `685_583`'s Python sorts and its Dafny
  takes a maximum by linear scan; `348_21` emulates a Python `set` with a linear
  scan.
- **A value the label omits.** The bound grows with an input's magnitude
  (`810_131`: binary search over the value `a*b`; `2607_90`: a loop over
  `hi - lo`). These change the label, never the code.

## Fields a reviewer should not over-trust

`true_class` held up against every row in `solutions-proved/` that carries a
machine-checked bound. **`cause` is softer**: it needs reasoning about the
Python's data shapes, not just its syntax, and review has overturned it in both
directions (`685_583`, `396_361`).

## Two rows are here for the code, not the label

`1950/1950_45.dfy` and `1950/1950_47.dfy` carry a `TRANSLATION AUDIT` header.
Their problem's `Input` dataclass types the coefficient as `float` while the
inputs carry up to 100 significant digits, so 19 of 42 stored tests fail for
the **original Python** too. No translation can exceed 23/42. The Dafny passes
7 and 19 of those 23: both cap the fractional part at 12 digits where the
Python uses `Decimal`.

To leave, they need 23/23 on the runnable tests; they then go to
`solutions-ungateable/` with an entry in `data/gate_ungateable.jsonl`.
`batches/gate-audit/` has the evidence.

## Open questions

- **Capped-value rows filed as constant.** The first audit filed these as label
  errors at O(1) or O(n) by treating a capped value as a constant, the
  opposite of `COMPLEXITY.md`'s rule: `1306_15`, `1306_197`, `1678_212`,
  `1722_66`, `1738_180`, `2065_128`, `2128_34`, `2482_13`, `2639_73`,
  `2639_117`, `2700_53`. Re-review them as one group under the value rule.
- **Correct but too slow to gate.** `1501_224` (in `solutions-ungateable/`)
  agrees on every test it finishes and times out on 16. The corpus has no
  ruling on whether a timeout-only `differs` counts against a row.
