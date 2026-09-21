# `solutions-disputed/` — label audit review queue

158 rows whose stated complexity label does not describe what the code costs.
**Queued for manual review; nothing here is a decision.** Each file keeps its
full original body with a header naming the audited class, the cause, the
confidence and the evidence, so a reviewer needs nothing else open.

Produced by `labelaudit.py` from agent verdicts that passed `checkverdicts.py`,
with every mismatch re-checked by the orchestrating session before the move.

> Renamed from `solutions-tofix/`. "To fix" overstated the verdict: 118 of the
> 152 rows need a **label** changed, not code. What is disputed is the label,
> and that is what the name now says.

## These rows are still in the dataset

Quarantined, not removed. Every gate runs on them, they keep their labels, and
they appear in `data/dataset.jsonl` like any other row. 12 of them also carry a
machine-checked complexity proof in `solutions-proved/` — the strongest input a
reviewer can have, and `checkverdicts.py` rejects any verdict that contradicts
one.

## The queue was re-filed when the cost model changed

`COMPLEXITY.md` § 1 charges `s[i := v]`, `m[k := v]` and set insertion `1`, by
stipulation. A verdict filed `cause: translation` *solely* because a Dafny
collection copies where CPython assigns in place is no longer a defect. `refile.py`
applied that, from a decision written per row in
`batches/cost-axioms/refile_decisions.jsonl`:

| | |
|---|---|
| left the queue | 31 |
| **joined** the queue | 5 |
| stayed, re-classified | 3 |
| net | 178 → 152 |

**Five rows moved the other way, and the plan did not predict it.** `1622_305`,
`1748_145`, `1367_88`, `2505_30` and `2854_107` were filed `ok` only because the
old per-write copy charge reproduced their `O(n**2)` label by accident — each
verdict says so in its own evidence, and says the Python is linear. Charge the
write `1` and the Dafny agrees with the Python while both disagree with the
label, so the label is what is wrong. An accidental agreement is not a passing
grade, and a model change exposes it in both directions.

Two rows that looked like clean returns were not. `1336_340` and `1981_62`
replace the Python's `sort` with a linear pass, so removing the copy charge does
not land them on their `O(nlogn)` labels — it drops them *below*, to `O(n)`.
They keep `cause: translation` in the too-fast direction. `2188_371` narrowed
from `both` to `label` for the same reason: its translation half dissolved, its
label half did not.

Every row that left the queue was re-gated: 26 strict rows `VALID`, 5 loose rows
`agrees`, and every file touched still passes `dafny verify`.


## The audit is complete — all 506 rows screened

Every row in `solutions/` has a verdict. 506 screened; after the re-file above,
347 `ok`, 152 `mismatch`, 7 `unsure`. The mismatches are here.

| cause | rows | before the re-file | what the repair is |
|---|---|---|---|
| `label` | 118 | 112 | BigOBench's label is wrong; the translation is faithful. Fix the label. |
| `translation` | 27 | 58 | The label is right about the Python. Fix the Dafny. |
| `both` | 6 | 7 | Neither matches. Both need work. |
| `harness` | 1 | 1 | Nothing is wrong. The dataset drew the measurement boundary elsewhere. Document it. |

`translation` more than halved, which is the whole point of the re-file: most of
that class was a container difference, not a defect. What is left is the four
shapes `batches/labelaudit/PROMPT.md` names — a replaced algorithm, a slice that
is a view in Dafny and a copy in Python, a concat rebuilt at every recursion
level, and a library call reimplemented as a loop.

Confidence on the mismatches: 108 high, 38 medium, 6 low.
22 rows carry `translation_defect` — the Dafny is in a worse class than the
Python — including three whose verdict is `ok`, where the label and the defect
happen to agree. Those are in `solutions/`, not here. The flag was cleared on
every row whose only "defect" was a copying collection.

17 rows land on `other`: their true class is outside the eleven-string
vocabulary (cubic, or a cost in a value rather than a size). Read `evidence` for
the real class.

### The one question the audit did not settle

A recurring group of rows takes only scalars the problem statement caps, and
loops a number of times that grows with the *value* of those scalars but not
with the input's *size*. This audit followed the prompt's rule — a capped value
is a constant — and filed them as label errors at O(1) or O(n).

If BigOBench measured by scaling those values, the original labels are right and
these findings invert. The rows are at least `1306_15`, `1306_197`, `1678_212`,
`1722_66`, `1738_180`, `2065_128`, `2128_34`, `2482_13`, `2639_73`, `2639_117`
and `2700_53`. **Decide the convention once, then re-file the group** — it is one
judgement, not eleven.

**One row makes the question concrete, and it is not in this queue.**
`solutions/1501/1501_224.dfy` is labelled `O(n)`, its whole input is one
integer n, and its loop runs about n/12 times. Its own tests supply n up to
**10^12**.

An earlier version of this section said neither implementation terminates and
that no gate can run on the row. Both claims were wrong, and they came from a
`difftest.py` budget bug rather than from the row. With the budget derived from
the test count, the row reports:

| | |
|---|---|
| comparable tests | 93 of 122 |
| agree | 77 |
| Dafny timed out where the Python finished | **16** |
| Python timed out, nothing to compare | 29 |

So the Python completes 93 of its own tests and the Dafny completes 77. The row
is `differs`, and every disagreement is a timeout — **zero wrong answers**. The
translation is correct wherever it finishes and slower than CPython on the same
input, which is what a bignum loop costs once it goes through the Dafny runtime.

That leaves the convention question intact and adds a second one:

- **Size reading:** the label is wrong. One integer input, work exponential in
  its length.
- **Value reading:** the label is right, and the row is a correct translation
  that the gate cannot certify because the emitted Python is too slow.

The second question is new: the corpus has no tier for *correct but too slow to
gate*. `differs` reads as a behavioural failure and this is not one.

Still the user's call. The twelve rows move as a group, and `1501_224` needs a
decision about what `differs`-by-timeout-only should mean.

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

`true_class` held up against every row in `solutions-proved/` that carries a
machine-checked bound. **`cause` is softer** — it needs reasoning about the
Python's data shapes, not just its syntax, and review already overturned it
twice, in both directions (`685_583`, `396_361`). Three rows are `confidence:
low` and are marked as such.

`true_class: other` means the true cost is outside the dataset's eleven-class
vocabulary — cubic, or a cost in a value rather than an input size. The class is
named in the evidence.

## These rows are still gated

`solutions-disputed` is in the root list of `validate.py`, `difftest.py`,
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

## There is no repair for a seq-update `translation` row

A `translation` row used to mean: the Python is O(n), the Dafny is O(n²),
because `s := s[i := v]` copies. That class is closed.
`batches/cost-axioms/PLAN.md` charges `s[i := v]` O(1) by stipulation, so the
Dafny and the Python are in the same class and the row is `ok`. Do not rewrite
it, and do not reach for another container.

The backend numbers are kept because they are still true of the artifact, and
because two rows depend on them:

| n | `s := s[i := v]` | `array<T>` `a[i] := v` |
|---|---|---|
| 4k | 0.059s | 0.004s |
| 8k | 0.204s | 0.003s |
| 16k | 0.795s | 0.003s |
| 32k | **3.374s** | **0.006s** |

Ratios of 3.4 / 3.9 / 4.2 per doubling: quadratic in the backend, O(1) per
update under the axioms. `solutions/2826_42` and `solutions/2128_34` write
tables far too large for the backend to copy per update, so those two keep an
`array<T>` and say so in a header comment. They are the corpus's only arrays.
Everywhere else the corpus is `seq`-only.

`Std.DynamicArray` was investigated as an alternative and is not used. It needs
`--standard-libraries` on every build path (`validate.py`, `difftest.py`, the
harness) and emits roughly a hundred `Std_*.py` files beside each row, in
exchange for a cost the axioms already grant `seq`.

**Both are backend facts, not charges.** Under the axioms `s + [x]` and
`s[i := v]` are each charged `1`, with no side condition about reading the
accumulator. `COMPLEXITY.md` § 1 is the model; its appendix is where these
timings belong.

## Four rows arrived on 2026-09-17, and they are a different kind of dispute

`810_131`, `1484_26`, `2381_156`, `2607_90`.

Every other row here is disputed because an audit read the code and disagreed
with the label. These four are disputed because **a convention was decided**
and the label fell on the other side of it.

A loop bounded by an input *value* now counts: the value is a parameter of the
bound, not a constant absorbed because the problem statement caps it. The
reasoning is that a capped value hides a constant of roughly 30 to 60, and a
label carrying a constant that size has stopped predicting growth, which is the
only thing a label is for. `COMPLEXITY.md` § 1 states it in full.

| row | label | class under the convention |
|---|---|---|
| `810_131` | `O(n)` | `O(n log v)` — binary search over the value `a*b` |
| `1484_26` | `O(n)` | `O(n * L)` — string comparison costs per character |
| `2381_156` | `O(1)` | `O(log n)` — `IntToString` costs the digit count |
| `2607_90` | `O(n)` | `O(n + (hi - lo))` — loop range read from input values |

**The translations are not at fault and their proofs are correct.** Each proof
stays in `solutions-proved/` and states the bound with the value term in it.
What is in dispute is only whether BigOBench's label describes that bound.

Resolving these four means changing the label, never the code. That makes them
the cleanest `cause: label` rows in the directory — the disagreement is fully
explained and there is nothing to re-measure.

## Two rows are here for the code, not the label

`1950/1950_45.dfy` and `1950/1950_47.dfy` carry a `TRANSLATION AUDIT` header
rather than a `LABEL AUDIT` one. What is disputed is the translation.

Their problem's `Input` dataclass types the coefficient as `float` while the
inputs carry up to 100 significant digits, so 19 of 42 stored tests fail for
the **original Python** too once routed through it. No translation can exceed
23/42. The Dafny passes 7 and 19 of those 23, so there are at least 16 and 4
genuine failures on top of the harness defect: both cap the fractional part at
12 digits where the Python uses `Decimal`.

To leave, they need 23/23 on the runnable tests and an entry in
`data/gate_exempt.jsonl` for the other 19. `batches/gate-audit/` has the
evidence.
