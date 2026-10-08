# Complexity model and proof guide

This file answers one question: what work does a proof count, and how does a
Dafny file prove an upper bound for that work?

## The model

The model is stipulated. It is not a timing claim about Dafny's Python, C#, or
Java backend. BigOBench labels were measured from CPython, so backend timings
and labels are different evidence.

Charge one unit for integer arithmetic and comparisons, sequence indexing and
length, and one unit of loop overhead per iteration. Charge one unit for every
character a string operation produces.

| operation | charge |
|---|---:|
| sequence index, length, update, append | 1 |
| sequence concatenation `s + t` | `|t|` |
| sequence slice `s[a..b]` | 1 (a view) |
| map lookup, membership, update, length | 1 |
| `Keys`, `Values`, `Items` | `|m|` |
| set membership and insertion | 1 |
| set iteration | `|s|` |
| `multiset(s)` | `|s|` |
| multiset equality | `|a| + |b|` |
| `Join(parts, sep)`, `sep` a source literal | `SumLen(parts) + |parts|` |
| `IntToString(x)` | `Digits(x)` |
| `JoinInts(xs, sep)`, `sep` a source literal | `SumDigits(xs) + |xs|` |
| recursive sequence/string helpers | argument length |
| sorting k items | `SortCost(k)`; prove it with `SortCostNLogN` |
| helper calls | the helper's `steps` |
| recursive helpers used for Python `**` | recursion depth |
| `Gcd(a, b)` (Python `math.gcd` or a Euclid loop) | `GcdSteps(a, b)`; bound it with `GcdStepsBound` |

`array<T>` is absent from the corpus. The two files that retain arrays explain
why in their headers; that is a backend note, not a different charge table.

### Decisions that often cause confusion

**Input values are parameters.** A loop bounded by an input value costs in that
value (`O(v)` or `O(log v)`), even when the problem statement caps it. Hiding a
30- or 60-iteration loop as constant would make the label useless as a growth
description.

**Integers are words; characters are not.** Arithmetic on an `int` costs one
unit however large the value, an idealised machine. Turning an `int` into text
costs one unit per character produced, `Digits(x)`, exactly as building any
other string does. So a value's size is free to compute with and paid for when
written out. Where the idealisation is visibly false (integers that outgrow a
machine word), record `tighter-costmodel`.

**Output length is its own parameter.** Every program that prints L characters
pays at least L steps, so output length bounds every possible solution from
below. Write an output term as `|output|` (prelude: `IntToStringDigits`,
`JoinLen`, `JoinIntsLen`), and compare only the rest of the bound with the
label: `steps <= 2 * NLogN(n) + 3 * |output| + 5` confirms `O(nlogn)`. An
additive `|output|` term never makes a row looser. A term that multiplies it
(`n * |output|`) or a `Digits` charge that never reaches the output (a digit sum,
a string comparison) is ordinary work and counts. If `|output|` dominates the
bound, say so in `relation_reason`.

**A label names each size it depends on.** A label variable is one
size: one list's length, one string's length, or one input value. A label must
be the tight class in those sizes, in both directions.

- `O(n)` over n strings that are each scanned is wrong, even though the cost is
  linear in the total text. It is `O(n*m)`.
- `O(n**2)` is one size squared. Two different sizes multiplied are `O(n*m)`.

`batches/labelaudit/PROMPT.md` § *Naming the sizes* has the full table.

## What a proof means

A proof adds a ghost `steps` counter, increments it for every charged action,
and states an upper bound such as `steps <= 2 * |a| + 2`. Dafny verifies that
postcondition for every input satisfying the method's preconditions. Ghost code
is erased from generated programs, so the same file remains runnable.

The bound is an upper bound, not a timing measurement. It is only as honest as
the charge table. If it and the BigOBench label differ, record the reason; do
not weaken the proof to make the label fit.

## Reading a proof

Start at `Solve` and list its loops and helper calls. For each one, identify
its size parameter and charge. Then read the invariants and `decreases` clause
that connect the counter to the input. Finally check the `ensures` bound and
run `python3 proofs.py` to verify the overlay.

A `decreases *` file may be safe on stored tests but has no termination argument
for an all-input complexity proof. Such rows remain in `solutions-unverified/`
until a real decreases measure is supplied.

## Why the backend is not the model

Dafny's Python translation may copy a sequence on update, while the stipulated
model charges that update one unit. Measuring a backend would make verdicts
depend on compiler version and language. The stipulated model keeps proofs
comparable; backend limitations stay in the record where they belong.

## Current proof overlay

`solutions-proved/` contains 321 checked proof files. It is an overlay: each
proof also has a normal translated row in `solutions/`, `solutions-disputed/`,
or `solutions-unscreened/`. The overlay proves the stated step bound; it does
not certify the behaviour gate or the label audit.
