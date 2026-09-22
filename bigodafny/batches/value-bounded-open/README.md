# `value-bounded-open/` — value-bounded rows with **no proof yet**

6 rows. Each one's real cost depends on how **large** an input is, while its
BigOBench label only counts how **many** inputs there are — and unlike the
eleven in `solutions-proved/value-bounded/`, nobody has managed to prove a
bound for it.

There are no `.dfy` files here, because there is nothing proved to hold.
`MANIFEST.jsonl` names each row, where it lives, and the obstacle that stopped
it. The rows themselves are untouched in `solutions/` and still pass their
behaviour gate; what is missing is a complexity proof, not a translation.

> Split out of `solutions-proved/value-bounded/` on 2026-09-22. Filing unproved
> rows under a directory whose name says `proved` was wrong.

## The rows

| row | label | what it would need |
|---|---|---|
| `1047_26` | `O(n)` | `colNum < Pow10(maxlen)` chained through `Pow10Mono` |
| `1306_126` | `O(n)` | the loop guard's inline sum hoisted into a ghost trace |
| `1944_50` | `O(n)` | a doubling-search invariant over `Pow2` / `Log2` |
| `1948_388` | `O(1)` | case-split invariants over `s*s` |
| `2819_926` | `O(n)` | `FloorDiv` and triangular-number bounds, four or five chained |
| `2926_50` | `O(n)` | a hoisted constant for a product of 53 primes, plus monotonicity |

Six rows, six different pieces of arithmetic. Proving `1948_388` teaches you
nothing about `2926_50`. That is the finding: unlike the `O(nlogn)` scaffold,
which was written once and then copied by later rows, none of this transfers.

`1948_388` is the clearest illustration. Its Python reads one number and calls
`sqrt` — one input, so the label counts `O(1)`. Dafny has no float `sqrt`, so
the translation searches: `while s*s < target { s := s+1; }`, about `sqrt(k)`
iterations. `k = 100` loops 28 times; `k = 10**18` loops a billion. Same one
input.

## `2423_48` left this directory, and it is the proof that the split is real

It was the one row here blocked by something reusable rather than its own
arithmetic: its trip count is `d[|d|-1].0 + 2`, the largest first component
after a sort, and `prelude.dfy` proved only `SortIsPermutation` — the output
holds the same elements as the input. Nothing said it was ordered, so the trip
count could not be tied to `pairs` at all.

`SortIsSorted` and `SortLastIsMax` went into the prelude on 2026-09-22. The row
was proved by hand the same day, after failing in two separate campaigns, and
is now in `solutions-proved/value-bounded/`. The proof's use of the new lemma
is four lines.

**The other six are unchanged, and that is the point.** Fixing the prelude
unblocked exactly one row, because the other six need their own arithmetic and
share nothing — with each other or with anything already in the corpus.

## How a row leaves

- **Proved.** Its proof goes to `solutions-proved/value-bounded/` and its
  manifest entry moves with it.
- **Reviewer decides the convention does not apply.** The value is genuinely
  capped by the problem statement in a way that keeps the constant small.
  Record the cap and the reasoning.
- **Reviewer decides the label is wrong.** The row goes to
  `solutions-disputed/` if it is not there already.

Nothing leaves by relaxing the value-versus-size convention for one row.
