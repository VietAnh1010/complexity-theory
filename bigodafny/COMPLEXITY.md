# Complexity model and proof guide

What a proof counts as work, and how a Dafny file proves a bound on it.

## The model

Costs are fixed by rule, not timed. Dafny's Python output may copy a sequence
on every update, but the model charges 1: timing a backend would tie every
verdict to one compiler and language.

Charge 1 for integer arithmetic and comparison, a sequence index or length,
each loop iteration, and each character a string operation produces.

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
| `Join(parts, sep)`, `sep` a string literal | `SumLen(parts) + |parts|` |
| `IntToString(x)` | `Digits(x)` |
| `ParseInt(s)` | undecided: 1 or `|s|` (`solutions-unsure/README.md`) |
| `JoinInts(xs, sep)`, `sep` a string literal | `SumDigits(xs) + |xs|` |
| recursive sequence/string helpers | argument length |
| sorting k items | `SortCost(k)`; prove it with `SortCostNLogN` |
| helper calls | the helper's `steps` |
| recursive helpers used for Python `**` | recursion depth |
| `Gcd(a, b)` (Python `math.gcd` or a Euclid loop) | `GcdSteps(a, b)`; bound it with `GcdStepsBound` |

The model has no `array<T>`. `2128_34` and `2826_42` use arrays; their
headers explain why.

### Rules people often get wrong

**An input value is a size.** A loop bounded by an input value costs `O(v)` or
`O(log v)`, even when the problem caps `v`. A 60-step loop is not "constant".

**Numbers are free to compute with, not to print.** `int` arithmetic costs 1
at any size. Turning an `int` into text costs 1 per digit (`Digits(x)`). Where
that is unrealistic (integers beyond a machine word), record
`tighter-costmodel`.

**Output length is its own size.** Printing L characters takes L steps under
any algorithm. Write that part as `|output|` (prelude: `IntToStringDigits`,
`JoinLen`, `JoinIntsLen`) and compare only the rest with the label:
`steps <= 2 * NLogN(n) + 3 * |output| + 5` confirms `O(nlogn)`.

- An added `|output|` term never counts against the label.
- `n * |output|`, or `Digits` for text never printed, is normal work.
- If `|output|` is the largest term, say so in `relation_reason`.

**The naming rule: a label names every size it depends on.** Each variable is
one list's length, one string's length, or one input value, and the class is
the tightest one.

- Scanning n strings is `O(n*m)`, not `O(n)`.
- `O(n**2)` is one size squared; two different sizes give `O(n*m)`.

`batches/labelaudit/PROMPT.md` § *Naming the sizes* has the full table.

## What a proof means

A proof adds a ghost `steps` counter, adds to it at every charged action, and
states a bound such as `steps <= 2 * |a| + 2`. Dafny checks it for every input
the `requires` allow. Ghost code is removed at compile time, so the file still
runs. If the bound disagrees with the label, record why; never weaken the
proof to fit.

A proof says nothing about whether the row passes its tests or its label is
right.

## Proof relations

How a proved bound compares with the label. The bound is an upper bound, so it
lands in the label's class, above it, or below it:

| Relation | The bound is… | because… |
|---|---|---|
| `confirms` | in the label's class | |
| `looser-slack` | above | the proof is loose; a tighter one wasn't tried |
| `looser-structural` | above | the Python really pays a cost the label leaves out, usually a loop over an input value |
| `looser-costmodel` | above | the model charges more than CPython pays |
| `looser-translation` | above | the Dafny does work the Python doesn't |
| `tighter-costmodel` | below | the model charges less than CPython pays, usually `int` arithmetic on huge values |
| `tighter-translation` | below | the Dafny does less work than the Python |
| `tighter-label` | below | the Python does no more either: the label is too high |

`vocab.py` is the source of this list. In a campaign trajectory record,
`relation_reason` explains a row's relation in words.

## Reading a proof

1. Start at `Solve`; list its loops and helper calls.
2. For each, find the size it depends on and its charge.
3. Read the invariants and `decreases` clauses tying the counter to the input.
4. Check the `ensures` bound; run `python3 proofs.py`.

A row with `decreases *` cannot carry a proof: nothing shows it stops on every
input.
