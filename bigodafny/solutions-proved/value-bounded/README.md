# `value-bounded/` — the label counts items, the code follows magnitudes

**14 rows, each with a machine-checked proof.** Rows in the same category with
**no** proof do not belong under a directory named `solutions-proved`; they are
in `batches/value-bounded-open/`, which has its own README and manifest.

A row belongs here when its real cost depends on **how large** an input is,
while its BigOBench label only counts **how many** inputs there are. The
clearest case is `1948_388`:

```python
k = int(input())
n = (sqrt(8*k+1) - 1) / 2          # label: O(1) -- one input, one sqrt
```

One number in, so counting items there is nothing to grow. But Dafny has no
float `sqrt`, so the translation searches: `while s*s < target { s := s+1; }`.
That runs about `sqrt(k)` times. `k = 100` loops 28 times; `k = 10**18` loops a
billion. Same one input.

Two different things are both called "input size":

| | |
|---|---|
| **size** | how many items you were handed |
| **value** | how large those items are |

BigOBench fitted its labels by profiling, which treats a capped value as
constant. `COMPLEXITY.md` § 1 decides the opposite, by the 2026-09-17
convention: a loop bounded by an input value is not constant, and the value
enters the bound as its own parameter. So the two disagree here by
construction, and this directory is where that disagreement is collected.

## This is an overlay, not a partition member

Same status as `solutions-proved/` itself. The
rows still live in `solutions/`, `solutions-disputed/` or wherever the
partition puts them; `MANIFEST.jsonl` gives each one's `row` path. Nothing was
taken out of the dataset.

Three of the fourteen proved rows also sit in `solutions-disputed/` —
`810_131`, `1484_26` and `2607_90`, moved there on 2026-09-17. Being here is
not the same as being disputed: this directory says *the proof carries a value
term*, the disputed queue says *somebody should change the label*.

## The failures do not transfer

That is the finding, and it lives in `batches/value-bounded-open/`, where the
seven rows with no proof are listed with what each would need. Six rows, six
different pieces of arithmetic; nothing carries from one to the next.

Contrast `O(nlogn)`. Sorting was hard once; somebody wrote the `CeilLog2`
recursion-tree argument, it went into the corpus, and later rows copied it —
three did exactly that in `prove-sample-4`. One payment, many rows.

The single exception was `2423_48`, which needed a fact about the prelude
rather than its own lemma. `SortIsSorted` and `SortLastIsMax` went into
`prelude.dfy` on 2026-09-22 and the row was proved the same day, after failing
in two campaigns. Its proof uses the new lemma in four lines:

```dafny
SortLastIsMax(pairs, less);       // last element is >= every element
SortKeepsElems(pairs, less);      // and is itself one of them
MaxFirstBounds(pairs);            // so its .0 is the largest first component
MaxFirstAttained(pairs);
```

One prelude lemma, one row. The other six in `batches/value-bounded-open/` were
untouched by it — they need their own arithmetic.

## How a row gets in

From a campaign, two ways:

- `relation: looser-structural` in a batch's `label_relation.jsonl`, where the
  reason names an input **value**. Move its proof file here.
- `obstacle: value-to-size` in a batch's `obstacles.jsonl`. No proof exists, so
  the row goes to `batches/value-bounded-open/MANIFEST.jsonl`, **not** here.

Either way, name the campaign that found it.

## How a row gets out

A reviewer decides one of:

1. **The label is wrong** — the row moves to `solutions-disputed/` (if it is
   not there already) and the label is corrected upstream.
2. **The convention should not apply here** — the value is genuinely capped by
   the problem statement in a way that makes the constant small. Record the cap
   and the reasoning; the row leaves this directory.
3. **The proof is just loose** — a tighter bound exists that does not carry the
   value term. Prove it; the row leaves.

Nothing leaves by having the convention relaxed for one row.

## Files

| file | what it is |
|---|---|
| `MANIFEST.jsonl` | every row: status, label, bound, where the row lives, why |
| `<pid>/<sid>.dfy` | the proof, with a `VALUE-BOUNDED` header |

## Two rows left on 2026-09-22

`2381_156` and `276_610` were here because their proofs charged `IntToString`
by the digit count of the printed value. `COMPLEXITY.md` now charges
`IntToString(x)` and `|IntToString(x)|` one step each, so neither label omits
anything and neither row is structural. Both returned to `solutions/` and their
proofs to `solutions-proved/<pid>/`, recorded `looser-slack`.

Both were then **re-proved tight** on the same day, so neither carries a digit
term any more:

    2381_156   steps <= 6              O(1),  confirms
    276_610    steps <= 24 * n + 2     O(n),  confirms

`276_610`'s proof charges each output part a constant `PART_CHARGE` instead of
measuring `SumLen`, which is what keeps `Join` from reintroducing the digit
count. Neither file defines a digit-counting ghost function any more, and that
is deliberate: one would put back exactly the term the charge decision removed.

Nothing else here rests on that charge: the other twelve turn on loops bounded
by input values, which the value-versus-size convention still counts.

## Two rows arrived on 2026-09-23

`prove-sample-7` filed `1043_358` and `794_794`, taking the directory to
thirteen.

    1043_358   8*|a_list| + 2*SumPos(a_list,|a_list|) + 3      O(n)
    794_794    30*|data| + 30*SumNN(data,|data|) + 3           O(n)

Both are the plainest form of the pattern. `1043_358` prints
`"2" + "3" * (v - 1)` once per test case, so the work per test is the input
value `v`. `794_794` loops `range(1, n)` and then prints `n` numbers, where `n`
is a per-test value read by `int(input())` — while the label's `n` counts test
cases. The two `n`s are different quantities, and only one of them is in the
label.

## One row arrived on 2026-09-24

`1678_68` (label `O(1)`) was filed when campaign 7's rerun proof replaced its
overlay proof:

    1678_68    rows + 15                                        O(1)

The row's `GcdEx` is recursive in the Python too. The earlier proof charged it
one step and proved 15. The rerun charges its recursion depth, as the charge
table does for any helper, and that depth grows with the input value `rows`.
The bound is loose: Euclid's depth is logarithmic.
