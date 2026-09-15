# `solutions-tofix/` — label audit review queue

46 rows whose stated complexity label does not describe what the code costs.
**Queued for manual review; nothing here is a decision.** Each file keeps its
full original body with a header naming the audited class, the cause, the
confidence and the evidence, so a reviewer needs nothing else open.

Produced by `labelaudit.py` from agent verdicts that passed `checkverdicts.py`,
with every mismatch re-checked by the orchestrating session before the move.

## The three causes, and why they need different repairs

| cause | count | what is wrong | repair |
|---|---|---|---|
| `label` | 30 | the **Python** is not the labelled class either | fix the label |
| `translation` | 15 | the Python matches its label; the **Dafny** does not | fix the translation |
| `harness` | 1 | both are right; the dataset drew the boundary differently | neither — document it |

`harness` is the subtle one. The Python reads stdin and pays to parse every
input, and BigOBench profiled the whole script. The Dafny's `Solve` takes those
inputs already parsed, so parsing sits outside the measured method. A Python
that does `b = list(map(int, input().split()))` and then reads only `b[0]` is
genuinely O(n+m) while its faithful Dafny is O(n). Nothing is wrong with either.

## Recurring shapes

- **A dimension that cannot vary.** `O(n*m)` where a `requires` pins row width
  (`276_1206`) or the body reads only fixed positions (`171_82`, `89_463`,
  `525_273`, `396_361`).
- **A loop bounded by a literal constant.** `531_3456` and `531_3499` loop
  `while i < 5`; `514_39` is bounded by 31. Labelled `O(n)` or worse, truly O(1).
- **A seq update inside a loop.** `s := s[i := v]` copies the whole sequence in
  Dafny and is O(1) in CPython, so the translation gains a factor of n
  (`209_103`, `223_3085`, `85_141`, `85_71`).
- **A dropped or added algorithm step.** `685_583`'s Python sorts and its Dafny
  takes a maximum by linear scan; `348_21` emulates a Python `set` with a linear
  scan.

## Fields a reviewer should not over-trust

`true_class` held up against every row in `solutions-verified/` that carries a
machine-checked bound. **`cause` is softer** — it needs reasoning about the
Python's data shapes, not just its syntax, and review already overturned it
twice, in both directions (`685_583`, `396_361`). Three rows are `confidence:
low` and are marked as such.

`true_class: other` means the true cost is outside the dataset's eleven-class
vocabulary — cubic, or a cost in a value rather than an input size. The class is
named in the evidence.

## These rows are still gated

`solutions-tofix` is in the root list of `validate.py`, `difftest.py`,
`precheck.py` and `proofs.py`, so the rows are still validated, still carry
their labels, and still count in `dataset.py`. Moving a row queues it for
review; it does not remove it from the dataset.
