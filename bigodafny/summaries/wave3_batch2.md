# Wave 3, batch 2

20 rows, `966_134` .. `1047_26`. Agent: Sonnet, 106k tokens, 32 tool calls.

| | |
|---|---|
| Agent reported | 20/20 valid |
| Independent audit | **20/20 valid** |
| Reverted | 0 |
| Needed extended timeout | 0 |
| Tests executed | 580 |

Classes: O(n) 10, O(n**2) 4, O(nlogn) 2, O(1) 2, O(n*m) 1, O(n+m) 1.

## Examples

- `1011_177` — Python computes `sqrt` in floating point and rounds. Dafny has no
  floats, so the condition `frac > 0.5` became the exact integer test
  `4*n > (2f+1)**2`.
- `1027_141`, `1027_207`, `1027_458` — float slope and cosine comparisons
  replaced with exact rational cross-multiplication, `dy1*dx2 == dy2*dx1`.
- `1029_119`, `1029_92` — Dafny's `int` has no bitwise operators, so a local
  bit-by-bit recursive `BitOr` was written.

## Findings

**No float in Dafny is the recurring theme, not a nuisance.** Three of the four
notable rows here are float-elimination. Rewriting a float comparison as exact
integer or rational arithmetic changes the answer wherever the Python relied on
rounding error. Every one passed its tests, so the rewrites are right, but this
is the category most likely to hide a silent wrong answer: the tests are the
only thing standing behind them.

**The exponential-recursion warning worked.** Wave 2 produced local `MaxOf`/
`MinOf` that recursed twice per level. This batch defines no local `Max`/`Min`
at all — every row used the prelude. Prevention beat detection: that bug passed
its tests last wave, so agents cannot find it themselves.

**The per-row tool-call budget held.** 32 calls for 20 rows, against 86 for the
wave-2 agent that thrashed. No rows abandoned.

## Carried forward

`ParseInt` is now hand-written in 9 files dataset-wide. It belongs in
`prelude.dfy`. Not added yet: agents currently running `include` that file, and
a compile error there would break all of them at once. Add it between waves.
