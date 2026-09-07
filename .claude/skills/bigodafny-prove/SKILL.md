---
name: bigodafny-prove
description: Prove a BigOBench row's time-complexity label in Dafny with a ghost step counter. Use when asked to prove, establish, or machine-check a complexity label, when working in solutions-verified/ or solutions-nlogn/, or when a label is suspected wrong. Covers the charging convention and the CeilLog2 recursion-tree argument.
---

# Proving the complexity label

Read the `bigodafny` skill first, and `bigodafny/COMPLEXITY.md` for the full
convention — this is the operating procedure, that is the contract.

`solutions/` proves **behaviour**: the Dafny reproduces the Python's stdout.
It says nothing about the label. `solutions-verified/` proves the **label**.

Testing cannot catch a wrong label. Three defects in this project produced
correct output, a wrong complexity, and green tests: a doubly-recursive min/max
(`T(n) = 2T(n-1)`), sibling reuse, and `set<T>` built in a loop.

## The technique

A ghost step counter with a proved upper bound.

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
  { i := i + 1; steps := steps + 2; }
  output := "";
  steps := steps + 1;
}
```

The `ghost` out-parameter is **erased at compile time** — verified: the emitted
Python is `def Solve(n, a__list)` with zero occurrences of `steps`. So one file
both runs under the test harness and carries a machine-checked proof.

## The charging convention

`steps` charges 1 per operation that is constant time **in Dafny's compiled
Python**: `int` arithmetic and comparison, `s[i]`, `|s|`, one unit of loop
overhead per iteration.

Anything else is charged its real cost:

| operation | real cost |
|---|---|
| `s + [x]`, `s + t` | `\|s\|`, `\|s\| + \|t\|` |
| `s + {x}` set insert | `\|s\|` — **measured**, not assumed |
| a helper call | the helper's own `steps` |

**Miscounting here is the entire risk.** An uncharged seq append inside a loop
turns a proved "O(n)" into a real O(n²) and Dafny still says verified. Prefer
array-backed accumulation with one `Join` at the end — which is what the
translations already do. A reviewer should check the charges before checking the
invariants.

Constants are free: the label is asymptotic, so `steps <= 7*n + 12` proves O(n).
Do not tune constants to look tight — take whatever the invariant supports.

## Logarithmic bounds

Dafny has no `log`. `solutions-nlogn/` proves the true O(n log n) for merge sort.
Two things make it work.

**Use a ceiling log, not a floor log.**

```dafny
ghost function CeilLog2(n: nat): nat
  decreases n
{ if n <= 1 then 0 else 1 + CeilLog2((n + 1) / 2) }
```

The recursive step is `ceil(n/2)`; both halves of a split of size `k` are at most
`ceil(k/2)`, so `CeilLog2(ceil(k/2)) == CeilLog2(k) - 1` holds *by definition*.
With floor-log that step is false at `k = 3` and the induction cannot close.

**Isolate every multiplication.** Z3 does not do nonlinear arithmetic. The whole
argument in one `calc` timed out at 30s. Splitting the two multiplication facts
into their own lemmas, so the solver never has to discover one, took it to 2.8s.

```dafny
lemma MulMonoRight(x: nat, p: nat, q: nat) requires p <= q ensures x * p <= x * q {}
lemma MulDistrib(a: nat, b: nat, k: nat, L: nat) requires a + b == k
  ensures a * L + b * L == k * L {}

lemma SortCostNLogN(k: nat) ensures SortCost(k) <= 2 * k * (CeilLog2(k) + 1) + 1
```

Keep the weaker proof. `solutions-verified/` retains the honest `O(n²)` fallback
for the two sort rows; `solutions-nlogn/` carries the tight bound on a copy.

## Procedure

1. Copy the row from `solutions/` into `solutions-verified/<PID>/<SID>.dfy`.
   Never instrument in place — the ghost version is a second artifact.
2. Add `ghost steps: nat` to the out-params and an `ensures` naming the bound in
   terms of the input, matching the label's shape.
3. Charge every operation per the table. Loop invariants relate `steps` to the
   counter.
4. `dafny verify --solver-path /usr/local/bin/z3 --verification-time-limit 30`.
5. `python3 validate.py --only <SID>` — the compiled output must be unchanged.
6. `python3 precheck.py <SID>` — every `requires` against every stored input.
7. `python3 proofs.py` — re-verifies everything and **exits non-zero on any
   `assume`**.

## What a proof claims

**Claims**: instrumented `steps` is bounded by that function of input size for
every input satisfying the preconditions. Over all inputs, not the stored tests.

**Does not claim**: that `steps` is wall-clock time. The bound is only as honest
as the charging convention.

**Against the label**: BigOBench's label is synthetic — regression over profiling
runs. Where a proof and the label disagree, **the proof is the stronger
statement. Record the disagreement; never adjust the proof to match the label.**

## Results so far

10 rows in `solutions-verified/`, 2 in `solutions-nlogn/`. 12/12 verify, zero
`assume`, 12/12 still pass their tests.

Two labels **proved wrong**, same cause both times: the `m` in `O(n*m)` names
nothing that varies. `1138_83`'s `m` is a scalar modulus; `1650_428`'s rows are
each exactly two tokens. True cost O(n) in both. 48 rows carry `O(n*m)`
dataset-wide; two of two examined were wrong — a reason for suspicion, not a rate.

`827_148` has no polynomial bound at all until values are capped: its inner
catch-up loop is data-dependent. The proof takes the problem's stated
`1 <= d_i <= 1000` as a precondition and folds the cap into the constant. The
label assumes the same thing silently.

`1484_82`'s trailing comparison loop is bounded by total string length, not `n`,
so it is charged against `SumLen(numbers)`. That term is real work, not slack.
