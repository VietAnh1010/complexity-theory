# Wave 3, batch 1

20 rows, `685_777` .. `960_63`. Agent: Sonnet, 120k tokens, 24 tool calls.

| | |
|---|---|
| Agent reported | 20/20 valid |
| Independent audit | **20/20 valid** |
| Reverted | 0 |
| Needed extended timeout | 0 |

Fewest tool calls of the wave, so the per-row budget cost nothing in quality.

## Examples

- `772_19`, `772_6` — segment tree. Dafny's `int` has no bitwise operators, so
  these use `((x as bv64) | (y as bv64)) as int`.
- `788_22` — power-of-two check, same cast pattern.
- `785_75` — `Sort` on tuples fails type inference without explicit lambda
  parameter types.

## Findings

**Two agents hit the tuple-`Sort` inference failure independently** (this batch
and batch 3). Neither knew about the other. The fix is the same both times:

```dafny
Sort(xs, (x: (int, int), y: (int, int)) => x.0 < y.0)
```

Without the annotations, `dafny translate py --no-verify` reports "type of the
receiver is not fully determined". Two independent discoveries means this
belongs in the agent prompt, not in a summary nobody reads mid-task.

**A loop-termination idiom worth recording.** Where `decreases` mixes a boolean
flag with a numeric bound, `decreases !flag, t` worked every time (`696_49`,
`704_351`, `788_76`) -- cheaper than proving the flag cannot fire without the
bound also shrinking, and the gate here is tests, not verification.

## Recurring gaps, measured across all 210 translations

| pattern | files |
|---|---|
| `ParseInt` hand-written | 9 |
| `bv64` bitwise casts | 3 |
| local `Max`/`Min` | 3 |
| `StringLess` | 2 |

These go into `prelude.dfy` between waves. Not during one: every running agent
`include`s that file, so a compile error there breaks all four at once.
