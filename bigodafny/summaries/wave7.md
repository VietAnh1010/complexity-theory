# Wave 7 — the last 80 strict rows

| batch | valid | verify |
|---|---|---|
| 1 | 20/20 | **20/20** |
| 2 | 20/20 | **20/20** |
| 3 | 20/20 | 18/20 |
| 4 | 20/20 | **20/20** |
| total | **80/80** | **78/80** |

**Every strict row is now translated.** The 104 stubs left in `solutions/` are
exactly the 100 `loose` and 4 `unvalidatable` rows, which no translation can
pass by byte-diff.

## Asking for verification up front changed everything

Earlier waves optimised for tests alone and reached **32%** on `dafny verify`.
This wave was told to spend ~3 extra tool calls per row discharging the
obligations Dafny raises with no specification written. It reached **97.5%**.

Writing the invariant while you still remember why the index is in range is
nearly free; retrofitting it is not.

The two failures use a list-as-stack DFS whose termination needs an
unvisited-node potential function, not an index bound. Batch 3's agent reported
19/20; an independent sweep found both `2854` rows failing, so 18/20 stands.

## Transferable fixes the agents found

- `invariant i <= n` where `n` is an unconstrained `int` parameter **fails on
  entry** — Dafny cannot assume `n >= 0`. Drop the upper bound. Dominant blocker.
- A loop that sets a break flag without advancing its counter fails `decreases`
  even though the flag halts it. Force the counter to its terminal value on the
  break path.
- Dafny forgets a `seq`'s length across a loop unless an invariant restates it.

## The prelude gap, fixed

`Sort` carried no length fact, so rows that sorted and then indexed had to
hand-roll a lemma — or `assume` it. Two agents flagged it independently.
`ensures |Sort(s, less)| == |s|` is now on the functions themselves (not a
separate lemma), so every call site gets it for free. Prelude verifies: 28
verified, 0 errors.

That removed all 8 `assume`s wave 7 introduced. Two were the sort-length fact;
the other six asserted an input shape mid-body and became a visible
`requires n >= 0 && |digits| == 3 * n`, checked against all 103 stored inputs
for both rows. **Wave 7 now contains zero `assume`s.**

It lifted no older row: the sweep went 143 -> 221, exactly the 78 wave-7 rows.
The fix helps code written to use it, not code already written around it.

## Final classification, rebuilt from scratch over all 532

    solutions/             clean: valid, verified, label unsuspected   180
    solutions-unverified/  valid; safety obligations open              237
    solutions-inexact/     complexity label suspect                    115
    solutions/ (stubs)     loose + unvalidatable, not translatable     104

529 of 532 translations pass their tests. Two failures are the parser-blocked
`1196` pair; the third, `1738_180`, is correct but slow — 32/32 at a larger
per-test budget.
