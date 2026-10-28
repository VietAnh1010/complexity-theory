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
| `seq(n, f)` | `n`, plus the cost of each `f(i)`, `0 <= i < n` |
| array `new T[n]`, `new T[n, m]` | `n`, `n * m`; `new T[n](f)` as `seq(n, f)`; index, update, `Length` 1 |
| `var x := e; body` | `e` plus `body` |
| a lambda | 0 where written; its body is charged where it is called |
| map lookup, membership, update, length | 1 |
| `Keys`, `Values`, `Items` | `|m|` |
| set membership and insertion | 1 |
| set iteration | `|s|` |
| `var x :| x in s` | 1: one step of iterating `s` |
| `multiset(s)` | `|s|` |
| multiset equality | `|a| + |b|` |
| `Join(parts, sep)`, `sep` a string literal | `SumLen(parts) + |parts|` |
| `IntToString(x)` | `Digits(x)` |
| `ParseInt(s)`, `SplitWs(s)` | `|s|`; `ParseInts(xs)` costs `SumLen(xs)` |
| `JoinInts(xs, sep)`, `sep` a string literal | `SumDigits(xs) + |xs|` |
| a function `F` the row defines | `F_steps(args)`: a ghost function with `F`'s parameters, `requires` and `decreases`, whose body is the cost of `F`'s body; a recursive call costs `F_steps` |
| sorting k items | `SortCost(k)`; prove it with `SortCostNLogN` |
| helper calls | the helper's `steps` |
| recursive helpers used for Python `**` | recursion depth |
| `Gcd(a, b)` (Python `math.gcd` or a Euclid loop) | `GcdSteps(a, b)`; bound it with `GcdStepsBound` |

A proof may charge a function call more coarsely, e.g. its argument length
for a helper that recurses once per element and does constant work each time.
That charge is within a constant factor of `F_steps`, so the class is the same.

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
- Writing is done once: format each value (`IntToString`, a hand-written
  base conversion that appends), assemble lines, `Join`. Anything beyond that
  is work: building a string by prepending (`c + acc` copies `acc` every
  step), or text built and thrown away.
- `n * |output|`, or `Digits` for text never printed, is normal work.
- If `|output|` is the largest term, say so in `relation_reason`.

**Input length is its own size too.** Reading `Solve`'s arguments costs one
step per character under any algorithm. Write it as an input term: `|s|` for a
`string`, `SumLen(xs)` for a `seq<string>`, `SumLen2(rows)` for a
`seq<seq<string>>`. `steps <= 4 * |a_list| + SumLen(a_list) + |output| + 3`
confirms `O(n)`.

- An added input term never counts against the label.
- Reading is done once: find each token's boundaries, then convert the token
  (a numeral in any base, prelude or hand-written). `BC23` read as column 55,
  row 23 is reading.
- Anything more is work: a second pass over a token, a separate format check,
  searching, comparing or counting over argument strings.

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

**The bound is one top-level `ensures steps <= E`.** `E` names only `Solve`'s
inputs and `|output|`:

- A case split goes inside `E`: `4 * (if n >= 1 then n else 0) + 6`, not two
  `ensures n >= 1 ==> ...` clauses.
- A repeated subterm becomes a ghost function, not an `ensures var x := ...`.
- No ghost out-parameter: a value the code computes, such as a running total,
  is bounded by a ghost function of the inputs.

`fuzzing/steptrace.py` evaluates `E` on each input it runs; any other form
leaves it no bound to compare `steps` with.

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
