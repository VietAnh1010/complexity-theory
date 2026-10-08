# `value-bounded/` — the label counts items, the code follows magnitudes

**22 rows, each with a machine-checked proof.** Rows in the same category with
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
constant. `COMPLEXITY.md` § 1 decides the opposite: a loop bounded by an input value is not constant, and the value
enters the bound as its own parameter. So the two disagree here by
construction, and this directory is where that disagreement is collected.

## This is an overlay, not a partition member

Same status as `solutions-proved/` itself. The
rows still live in `solutions/`, `solutions-disputed/` or wherever the
partition puts them; `MANIFEST.jsonl` gives each one's `row` path. Nothing was
taken out of the dataset.

All 22 rows also sit in `solutions-disputed/`. Being here is
not the same as being disputed: this directory says *the proof carries a value
term*, the disputed queue says *somebody should change the label*.

## The rows

22 rows. `MANIFEST.jsonl` has each one's bound, where the row lives, and
why its bound names a value. History: `../../CHANGELOG.md`.

| row | label | found by |
|---|---|---|
| `1043_358` | `O(n)` | prove-sample-7 |
| `1386_19` | `O(nlogn)` | prove-sample-2, prove-sample-5 |
| `1386_38` | `O(n)` | prove-sample-2 |
| `1484_26` | `O(n)` | prove-sample |
| `1580_12` | `O(n+m)` | prove-sample-6 |
| `1678_68` | `O(1)` | prove-sample-7 rerun |
| `1820_180` | `O(n)` | prove-sample-4 |
| `1867_16` | `O(n)` | prove-sample-3 |
| `1871_291` | `O(n)` | prove-sample |
| `1915_158` | `O(n+m)` | prove-sample |
| `1948_388` | `O(1)` | prove-sample-4, prove-sample-6 (failed then closed) |
| `2128_34` | `O(n**2)` | prove-sample |
| `2254_6` | `O(n)` | prove-sample |
| `2358_421` | `O(n)` | prove-sample-4 |
| `2423_48` | `O(nlogn)` | prove-sample-3, prove-sample-4 (failed both) |
| `2607_90` | `O(n)` | prove-sample |
| `305_76` | `O(nlogn+mlogm)` | prove-sample-3 |
| `704_351` | `O(1)` | prove-sample-3 |
| `794_794` | `O(n)` | prove-sample-7 |
| `810_131` | `O(n)` | prove-sample |
| `2942_55` | `O(n)` | main agent, 2026-10-01 |
| `305_284` | `O(n+m)` | main agent, 2026-10-01 |

Three causes recur:

- **A loop over a value.** `1580_12` loops until `b*i` reaches `a*c`;
  `794_794` loops `range(1, n)` where `n` is a per-test value, while the
  label's `n` counts test cases; `305_284` searches `range(p, q)`, a
  difference of input values.
- **Output whose length is a value.** `1043_358` prints `"2" + "3" * (v - 1)`
  per test; `2254_6` prints a string of length `n_i`.
- **Euclid's depth.** `1386_19`, `1386_38`, `1871_291`, `1915_158` and
  `1678_68` charge `Gcd` (or `GcdEx`) its recursion depth, a log of the
  values. Those bounds are loose: the running gcd only shrinks, so the depths
  telescope to `O(n + log max)`. The tighter bound still names a value.
  `2942_55` computes `2**m` by squaring, a depth in each exponent's bit
  length (`TokBits`).

## The failures do not transfer

That is the finding, and it lives in `batches/value-bounded-open/`, where the
rows with no proof are listed with what each would need. Each needs different
arithmetic; nothing carries from one to the next.

Contrast `O(nlogn)`. Sorting was hard once; somebody wrote the `CeilLog2`
recursion-tree argument, it went into the prelude, and later rows reuse it. One
payment, many rows.

The single exception was `2423_48`, which needed a fact about the prelude
rather than its own lemma (`SortLastIsMax`):

```dafny
SortLastIsMax(pairs, less);       // last element is >= every element
SortKeepsElems(pairs, less);      // and is itself one of them
MaxFirstBounds(pairs);            // so its .0 is the largest first component
MaxFirstAttained(pairs);
```

## How a row gets in

From a campaign, two ways:

- `relation: looser-structural` in a batch's `label_relation.jsonl`, where the
  reason names an input **value**. Move its proof file here.
- `obstacle: value-to-size` on a batch's trajectory record. No proof exists, so
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
4. **The proof stops verifying** — it leaves for `batches/value-bounded-open/`.

Nothing leaves by having the convention relaxed for one row.

## Files

| file | what it is |
|---|---|
| `MANIFEST.jsonl` | every row: label, bound, where the row lives, why |
| `<pid>/<sid>.dfy` | the proof, with a `VALUE-BOUNDED` header |
