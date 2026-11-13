# Wave 3, batch 3

20 rows, `1047_641` .. `1134_928`. Agent: Sonnet, 110k tokens, 37 tool calls.

| | |
|---|---|
| Agent reported | 20/20 valid |
| Independent audit | **20/20 valid** |
| Reverted | 0 |
| Needed extended timeout | 0 |

## Findings

**The dataclass can disagree with the Python about what `n` means.** For problem
1073, the generated `Input.n` is `raw_first_int - 1`, while the Python source
reads the raw value and does not subtract. Both `1073_645` and `1073_822` need
`var rawN := n + 1;` before the original algorithm runs.

This is the most dangerous class of defect found so far. The signature is
correct, the translation is correct, and the row still produces wrong answers,
because the argument does not hold the value the Python thought it read. It was
caught only because two solutions of the same problem shared the shift while
neither Python source subtracted.

Nothing detects this in general. `from_str` is LLM-generated per problem and may
transform values, not just split them. Tests catch it here; a row with weak
tests would not.

**Tuple-typed `Sort` needs explicit lambda parameter types.**

```dafny
Sort(xs, (x: (int, int), y: (int, int)) => x.0 < y.0)
```

Without the annotations `dafny translate py --no-verify` fails inference with
"type of the receiver is not fully determined". A usage note, not a prelude gap.

## Carried forward

Worth a targeted check in later waves: for each problem, does `Input.from_str`
transform any field rather than just parse it? A cheap version is to compare
`Input.from_str(x).__repr__()` against `x` — 22 rows already fail that
round-trip, measured at Step 0, and problem 1073 is the kind of case it flags.
