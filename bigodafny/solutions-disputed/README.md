# `solutions-disputed/` — label audit review queue

178 rows whose stated complexity label does not describe what the code costs.
**Queued for manual review; nothing here is a decision.** Each file keeps its
full original body with a header naming the audited class, the cause, the
confidence and the evidence, so a reviewer needs nothing else open.

Produced by `labelaudit.py` from agent verdicts that passed `checkverdicts.py`,
with every mismatch re-checked by the orchestrating session before the move.

> Renamed from `solutions-tofix/`. "To fix" overstated the verdict: 112 of the
> 178 rows need a **label** changed, not code, and under
> `batches/cost-axioms/PLAN.md` a large part of the `translation` group needs
> nothing at all. What is disputed is the label, and that is what the name now
> says.

## These rows are still in the dataset

Quarantined, not removed. Every gate runs on them, they keep their labels, and
they appear in `data/dataset.jsonl` like any other row. 12 of them also carry a
machine-checked complexity proof in `solutions-proved/` — the strongest input a
reviewer can have, and `checkverdicts.py` rejects any verdict that contradicts
one.

## The cost model changed after most of these were filed

`batches/cost-axioms/PLAN.md` replaced the measured cost model with a
stipulated one: `s[i := v]`, `m[k := v]` and set insertion are all O(1),
independent of backend. A verdict of `cause: translation` filed *solely* because
a Dafny collection copies where CPython assigns in place is no longer a defect —
the label was right and so is the translation.

Re-filing those rows is step 3 of that plan and has **not** been run, because it
changes verdicts already queued for manual review. Expect roughly 30–40 of the
58 `translation` rows to return to `solutions/` when it is. The 112 `label` rows
are untouched by the switch: they were never about backend cost.


## The audit is complete — all 506 rows screened

Every row in `solutions/` has a verdict. 506 screened, 321 `ok`,
178 `mismatch`, 7 `unsure`. The mismatches are here.

| cause | rows | what the repair is |
|---|---|---|
| `label` | 112 | BigOBench's label is wrong; the translation is faithful. Fix the label. |
| `translation` | 58 | The label is right about the Python. Fix the Dafny. |
| `both` | 7 | Neither matches. Both need work. |
| `harness` | 1 | Nothing is wrong. The dataset drew the measurement boundary elsewhere. Document it. |

Confidence on the mismatches: 129 high, 43 medium, 6 low.
52 rows carry `translation_defect` — the Dafny is in a worse class than the
Python — including some whose verdict is `ok`, where the label and the defect
happen to agree. Those are in `solutions/`, not here.

23 rows land on `other`: their true class is outside the eleven-string
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

**One row settles it empirically, and it is not in this queue.** The first full
run of `difftest.py --loose` (100 rows, 95 agree, 4 untranslatable) turned up a
single `error: TimeoutExpired`: `solutions/1501/1501_224.dfy`, labelled O(n).
Its whole input is one integer n, and its loop runs about n/12 times. Its own
tests supply n up to **10^12**, so neither the Dafny nor the original Python
terminates — the row burned a 1800s budget without finishing one test.

Under the size reading the label is wrong: the input is one integer, so the work
is exponential in the input's length. Under the value reading the label is right
and the row is simply untestable at its own inputs. Either way the row is in
`solutions/` claiming to be clean while no gate can run on it, which is the
same situation `solutions-untranslated/` exists to name.

That makes the convention question concrete rather than academic, and it is
still the user's call: the rows above move as a group, and `1501_224` either
joins them or joins the untranslatable tier.

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
