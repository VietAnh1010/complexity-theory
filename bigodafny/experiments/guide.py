"""The proving methodology both arms receive, scrubbed.

Distilled from `bigodafny/COMPLEXITY.md`. Everything that could name an answer
is removed: row ids, complexity labels of specific rows, and the names of the
repository directories that hold finished proofs. Both arms get the identical
file, so methodology cannot be a confound between them.

    python3 experiments/guide.py > /tmp/GUIDE.md
"""
GUIDE = r"""# Proving a time-complexity bound in Dafny

You are given a Dafny method `Solve` that reproduces a Python program's stdout.
Your job is to prove an upper bound on how much work it does.

## The technique: a ghost step counter

Add a `ghost` out-parameter and an `ensures` that bounds it.

```dafny
method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * |a_list| + 2          // linear in |a_list|
{
  steps := 1;
  var i := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant steps == 2 * i + 1
    decreases |a_list| - i
  { i := i + 1; steps := steps + 2; }
  output := "";
  steps := steps + 1;
}
```

`ghost` is erased at compile time, so the program still runs and still produces
the same output. `dafny verify` discharges the bound.

## The charging convention

`steps` charges **1 per operation that is constant time in Dafny's compiled
Python**: `int` arithmetic and comparison, `s[i]`, `|s|`, and one unit of loop
overhead per iteration.

Anything else is charged its real cost:

| operation | real cost |
|---|---|
| `s + [x]` (seq append) | `\|s\|` |
| `s + t` (concat) | `\|s\| + \|t\|` |
| `s + {x}` (set insert) | `\|s\|` -- measured, not assumed |
| a call to a helper | that helper's own `steps` |

**Miscounting here is the entire risk.** An uncharged seq append inside a loop
turns a proved linear bound into a real quadratic one, and Dafny still reports
verified. Charge the append, or restructure to an array with one `Join` at the
end. A reviewer checks the charges before the invariants.

## Constants are free

The claim is asymptotic. `steps <= 7 * n + 12` establishes linear just as well
as `steps <= n`. Take whatever the invariant supports; do not tune constants to
look tight. Tuning wastes the run.

## Logarithmic bounds

Dafny has no `log`. Define a **ceiling** log:

```dafny
ghost function CeilLog2(n: nat): nat
  decreases n
{ if n <= 1 then 0 else 1 + CeilLog2((n + 1) / 2) }
```

The recursive step is `ceil(n/2)`, and both halves of a split of size `k` are at
most `ceil(k/2)`, so `CeilLog2(ceil(k/2)) == CeilLog2(k) - 1` holds by
definition. With a floor log that step is false at `k = 3` and the induction
cannot close.

**Isolate every multiplication.** Z3 does not do nonlinear arithmetic well. A
whole recursion-tree argument in one `calc` times out; the same argument with
each multiplication fact in its own lemma finishes in seconds.

```dafny
lemma MulMonoRight(x: nat, p: nat, q: nat) requires p <= q ensures x * p <= x * q {}
lemma MulDistrib(a: nat, b: nat, k: nat, L: nat) requires a + b == k
  ensures a * L + b * L == k * L {}
```

## The bound must still mention the input

A problem statement that caps a value -- `1 <= n <= 10^9` -- makes every loop it
controls run a bounded number of times, so `steps <= 20000000000` is provable
for almost anything here. It is also worthless: it describes no relationship
between input and work. A bound whose expression does not mention the input at
all is rejected unless the method genuinely has no input-dependent loop.

State the bound in the input's size, and put the cap in the constant factor --
`steps <= 1000 * n + 20`, not `steps <= 20000000000`.

## When there is no bound

Some loops are data-dependent and have no bound in the input *size* at all --
their trip count depends on input *values*. If the problem statement caps those
values, add the cap as a `requires` on `Solve` and fold it into the constant.
Say in your result that you did, and which cap. That is a real finding, not a
failure.

## What "refutes" can and cannot mean

A step counter proves an upper bound, so it can only refute a claimed class by
proving a strictly SMALLER one -- the program is faster than claimed. You
cannot show a program is slower than claimed this way; that needs a lower
bound, and nothing here produces one.

So if you charge a concat honestly, land on n^2, and the claim was O(n): you
have proved a bound the claim already satisfies. Set `verdict` to `proves`,
record the bound, and put "I believe the true cost is quadratic because ..." in
`notes`. Reserve `refutes` for a bound strictly tighter than the claim.

## What a proof claims

**Claims**: the instrumented `steps` is bounded by that function of the input,
for every input satisfying the preconditions -- not just the tested ones.

**Does not claim**: that `steps` is wall-clock time. The bound is only as honest
as the charging convention above.

## The vocabulary of answers

Every example in this experiment has a complexity drawn from exactly this list.
Answer with one of these strings, verbatim:

    O(1)   O(logn)   O(n)   O(n+m)   O(nlogn)   O(n*m)   O(n**2)
    O(n+mlogm)   O(nlogn+mlogm)   O(n+m)log(n+m)   O(n**2+m**2)

Here `n` and `m` are the sizes of the inputs the program reads. Which argument
of `Solve` plays the role of `n` is not declared anywhere -- decide it from the
code and say so in your result. That ambiguity is real: two claims in this
corpus have already been disproved because their `m` named a scalar that does
not vary with input size.

## Rules

- **Never `assume`**, including `assume {:axiom}`. It silences an obligation
  instead of discharging it, and the file still reports 0 errors. An unfinished
  proof is worth more than a hollow one.
- **Change no executable code.** Only ghost declarations, `steps` assignments,
  `invariant`, `decreases`, `ensures`, `requires`, and `lemma`s. A bound made
  true by altering the algorithm is not a bound on this program.
- `dafny verify` prints `verifier finished with N verified, M errors`. Only
  `0 errors` is a pass. Note that a lemma which times out proves nothing, while
  its callers may still report verified -- check for timeout lines too.
"""

if __name__ == "__main__":
    print(GUIDE)
