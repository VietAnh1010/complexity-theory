# `value-bounded/` — the label counts items, the code follows magnitudes

**18 rows queued for review.** 11 have a machine-checked proof here; 7 have no
proof yet and are listed in `MANIFEST.jsonl` with the obstacle that stopped
them.

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

Same status as `solutions-proved/` itself and `solutions-proved/nlogn/`. The
rows still live in `solutions/`, `solutions-disputed/` or wherever the
partition puts them; `MANIFEST.jsonl` gives each one's `row` path. Nothing was
taken out of the dataset.

Four of the eleven proved rows also sit in `solutions-disputed/` — `810_131`,
`1484_26`, `2381_156`, `2607_90` moved there on 2026-09-17 — and `276_610`
followed on 2026-09-22. Being here is not the same as being disputed: this
directory says *the proof carries a value term*, the disputed queue says
*somebody should change the label*.

## The failures do not transfer, and that is the finding

Six unresolved rows, six different pieces of arithmetic:

| row | what it would need |
|---|---|
| `1948_388` | case-split invariants over `s*s` |
| `1047_26` | `colNum < Pow10(maxlen)` chained through `Pow10Mono` |
| `1944_50` | a doubling-search invariant over `Pow2` / `Log2` |
| `2819_926` | `FloorDiv` and triangular-number bounds, four or five chained |
| `2423_48` | a sortedness lemma, which `prelude.dfy` does not have |
| `2926_50` | a hoisted constant for a product of 53 primes, plus monotonicity |

Contrast `O(nlogn)`. Sorting was hard once; somebody wrote the `CeilLog2`
recursion-tree argument, it went into the corpus, and later rows copied it —
three did exactly that in `prove-sample-4`. One payment, many rows.

Nothing like that exists here. Proving `1948_388` teaches you nothing about
`2926_50`.

`2423_48` is the sharpest case, because what is missing is not a proof but a
**fact about the prelude**. Its loop runs to `d[|d|-1].0 + 2`, the largest
first component after a sort. `prelude.dfy`'s `Sort` proves only that its
output is a permutation of its input — `SortIsPermutation` — and never that the
output is ordered. So Dafny cannot be told that the last element is the
maximum, and the trip count cannot even be *named*, let alone bounded. Adding
`SortIsSorted` to the prelude would unblock it and any row like it. That is the
one piece of work here that would transfer.

## How a row gets in

From a campaign, two ways:

- `relation: looser-structural` in a batch's `label_relation.jsonl`, where the
  reason names an input **value**. Move its proof file here.
- `obstacle: value-to-size` in a batch's `obstacles.jsonl`. No proof exists, so
  add the row to `MANIFEST.jsonl` with `status: unresolved`.

Either way, append to `MANIFEST.jsonl` and say which campaign found it.

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
