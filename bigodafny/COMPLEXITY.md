# Proving the complexity label

`solutions/` proves behaviour: the Dafny reproduces the Python's stdout on
stored tests. It says nothing about the complexity label each row carries. Three
defects found in this project produced correct output, wrong complexity, and
green tests — a doubly-recursive min/max, sibling reuse, and `set<T>` built in a
loop. Testing cannot catch any of them.

`solutions-verified/` proves the label.

## The technique

A **ghost step counter** with a proved upper bound.

```dafny
method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * |a_list| + 2          // O(n)
{
  steps := 1;
  var i := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant steps == 2 * i + 1
    decreases |a_list| - i
  {
    i := i + 1;
    steps := steps + 2;
  }
  output := "";
  steps := steps + 1;
}
```

`dafny verify` discharges the bound. The `ghost` out-parameter is **erased at
compile time** — verified: the emitted Python is `def Solve(n, a__list)` with
zero occurrences of `steps`. So one file both runs under the test harness and
carries a machine-checked complexity proof.

## The counting convention

`steps` charges **1 per elementary operation**, where elementary means constant
time in Dafny's compiled Python:

- arithmetic and comparison on `int`
- `seq` indexing `s[i]` and length `|s|`
- one unit of loop overhead per iteration

Operations that are **not** constant time must be charged their real cost:

| operation | real cost | charge |
|---|---|---|
| `s + [x]` (seq append) | O(\|s\|) | `\|s\|`, or avoid it |
| `s + t` (concat) | O(\|s\|+\|t\|) | `\|s\| + \|t\|` |
| `s + {x}` (set insert) | **O(\|s\|)** — measured | `\|s\|`, or avoid it |
| a call to a helper | its own bound | the helper's `steps` |

Miscounting here is the whole risk: an uncharged `seq` append inside a loop
turns a proved "O(n)" into a real O(n**2), and Dafny will still say verified.
So prefer array-backed accumulation and `Join` once at the end, which is what
the translations already do.

## What a proof does and does not claim

**Claims.** The instrumented `steps` is bounded by the stated function of the
input size, for every input satisfying the preconditions. This is a proof over
all inputs, not a measurement on the stored tests.

**Does not claim.** That `steps` equals wall-clock time. The bound is only as
honest as the charging convention above. A reviewer checking one of these files
should check the charges before checking the invariants.

**Relation to the label.** BigOBench's label is synthetic — regression over
profiling runs. A proved bound and the label can disagree, and the proof is the
stronger statement. Where they disagree, record it; do not adjust the proof to
match the label.

## Logarithmic bounds

Dafny has no `log`. `solutions-nlogn/` proves the true O(n log n) for merge sort
with a recursion-tree argument. Two things make it work.

**Use a ceiling log, not a floor log.**

```dafny
ghost function CeilLog2(n: nat): nat
  decreases n
{ if n <= 1 then 0 else 1 + CeilLog2((n + 1) / 2) }
```

The recursive step is `ceil(n/2)`. Both halves of a split of size k are at most
`ceil(k/2)`, and `CeilLog2(ceil(k/2)) == CeilLog2(k) - 1` then holds *by
definition*. With floor-log that step is false at k = 3: `floor(log2 2) = 1`,
not `floor(log2 3) - 1 = 0`. The induction cannot close.

**Isolate every multiplication.** Z3 does not do nonlinear arithmetic well. The
first attempt timed out at 30s with the whole argument in one `calc`. Splitting
the two multiplication facts into their own lemmas —

```dafny
lemma MulMonoRight(x: nat, p: nat, q: nat) requires p <= q ensures x * p <= x * q
lemma MulDistrib(a: nat, b: nat, k: nat, L: nat) requires a + b == k
  ensures a * L + b * L == k * L
```

— so the solver never has to discover one, took it to 2.8s. The result:

    SortCost(k) <= 2 * k * (CeilLog2(k) + 1) + 1

## Constants

The label is asymptotic, so any constants are acceptable: `steps <= 7*n + 12`
proves O(n). Do not tune constants to look tight — pick whatever the invariant
supports.
