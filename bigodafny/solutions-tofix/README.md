# `solutions-tofix/` — label audit review queue

118 rows whose stated complexity label does not describe what the code costs.
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

## A `translation` row can be too FAST, and that is the worse defect

Both directions land in the queue as `cause: translation`, and they need
opposite repairs. The schema only names one of them — `translation_defect: true`
marks the Dafny as *slower* — so the other direction has to be read off the
verdict itself: `cause: translation` where the audited class is **better** than
the stated label.

    label O(nlogn) -> audited O(n)   the Dafny is faster than the Python

That is not a win. `bigodafny/CLAUDE.md` § "Translate the algorithm, not just
the behaviour" forbids it, and it is invisible to both gates: the tests pass
because the output is right. The row then claims a complexity it does not run,
which is the one thing the dataset exists to get right.

Confirmed by reading both sources:

| row | what the Python does | what the Dafny does |
|---|---|---|
| `1368_67` | `t = sorted(s)`, then `s != t` | one adjacent-pair scan, no `Sort` call |
| `1470_470` | `ar = sorted(ar)` | two linear scans with early break |
| `1470_325` | `del l[0]` in a loop — the real O(n**2) | a two-pointer `lo`/`hi` scan |
| `685_583` | `sorted(a)` then `a[-1]` | two linear maxima |

**Repair: restore the Python's algorithm, do not change the label.** The label
is correct about the program BigOBench measured. Putting the sort back is the
fix; relabelling the row to match a faster translation would bake the defect in.

Eight rows on record currently read this way. Check the direction before
starting: `cause: translation` with the audited class *worse* than the label is
the ordinary case in the table below, and its repair is the opposite one —
change the data structure, keep the algorithm.

## Choosing the repair for a `translation` row

Measured in Dafny 4.11.0's Python backend, with a known-quadratic control in the
same table (min of 3 runs, interpreter startup subtracted):

| n | `s := s[i := v]` | `array<T>` `a[i] := v` | `DynamicArray.Put` | `DynamicArray.Push` |
|---|---|---|---|---|
| 4k | 0.059s | 0.004s | 0.002s | 0.011s |
| 8k | 0.204s | 0.003s | 0.010s | 0.008s |
| 16k | 0.795s | 0.003s | 0.018s | 0.017s |
| 32k | **3.374s** | **0.006s** | 0.041s | 0.031s |

The seq update ratios are 3.4 / 3.9 / 4.2 per doubling — quadratic. `array<T>`
is flat and about 560x faster at n = 32k.

**Use `array<T>` with `a[i] := v`.** It is faithful to CPython's `lst[i] = v`,
needs no new build flag, and the corpus already uses it.

`Std.DynamicArray` does exist in Dafny 4.11's standard library (`Push`, `Put`,
`PopFast`, `Ensure`) and both `Push` and `Put` measure linear. It is the right
tool only where a row appends with no known final length, because `array<T>`
needs its size up front. The cost of reaching for it: `--standard-libraries` has
to be added to every build path (`validate.py`, `difftest.py`, the harness) and
it emits roughly a hundred `Std_*.py` files beside each row.

**Seq append is not the problem.** `s := s + [x]` is O(1) amortised — the
backend defers the concat. The quadratic patterns are the seq *update* above and
an append whose loop also reads `s[i]`, which forces a flatten on every
iteration.
