# Verification pass, wave 1 of 3

Retrofitting proofs onto 80 of the 237 translations written before verification
was a goal.

**78 of 80 now verify. All 80 still pass their tests. Zero `assume`.**

| batch | verify | tests |
|---|---|---|
| 1 | 20/20 | 20/20 |
| 2 | 20/20 | 20/20 |
| 3 | 20/20 | 20/20 |
| 4 | 18/20 | 20/20 |

`solutions/` is now **258/258 verified**, up from 180.

The two failures (`888_179`, `888_6`) sweep two pointers over an array doubled
to length `2n`; safety depends on `x <= sum(d)` propagating through a sliding
window — a prefix-sum argument, not a loop invariant.

## Retrofitting is nearly as effective as writing it in

Wave 7 wrote verification in from the start and got 97.5%. This pass retrofitted
and got 97.5%. The expected penalty did not appear. What the rows needed was
almost always a fact the author already knew and had not written down.

## The cost: 109 preconditions

70 of the 80 rows needed at least one `requires`. That is the honest price —
adding a precondition narrows the contract until the obligation is trivial, so
each one must be a guarantee the problem actually makes.

Every clause was checked against every stored input, not trusted:

    ok         104
    VIOLATED     1
    unchecked    2   (hand-read: both hold on all 77 inputs)

The one violation is instructive. `577_509` states
`forall t :: 1 <= numbers_list[t] <= 1000000000`, which is the problem's
constraint **verbatim** — "each test case contains a single integer n
(1≤ n≤ 10^9)". Three generated tests feed `n = 1000001000`. The precondition is
right and the test data is out of spec.

That is the third time BigOBench's generated tier has been found outside its own
problem's stated constraints, after `827_148` and `1254_187`.

## Recurring shapes, all three agents independently

- An unconstrained `int` parameter paired with a `seq`, needing `n == |xs|`.
- Row shape on nested input: `forall k :: 0 <= k < |xs| ==> |xs[k]| >= c`.
- Positivity a problem guarantees but the signature never stated.

`signature.py` could emit `requires n == |xs|` when the dataclass gives a
parallel `(n, seq)` pair, which would preempt most of them.

## Next central fix

`Sort` has a length `ensures` but no membership one. Two rows hand-wrote a
`SortElems` lemma to show sorted values stay within the input's bounds. Adding
`ensures forall x :: x in Sort(s, less) ==> x in s` would remove that tax.
