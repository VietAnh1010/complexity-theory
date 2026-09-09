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
| `s + [x]`, appends only | `1` — **measured**: the backend defers the concat |
| `s + [x]`, with `s[i]` read between appends | `\|s\|` — the read forces a flatten |
| `s + {x}` set insert | `\|s\|` — **measured**, not assumed |
| `Join(parts, sep)` | **superlinear (~L^1.2)** — do not charge it; see below |
| a recursive prelude function over a seq or string | its length |
| a helper call | the helper's own `steps` |

**Miscounting here is the entire risk, and it runs both ways.** Undercharging
turns a real O(n²) into a proved "O(n)" and Dafny still says verified.
Overcharging puts a correct label out of reach and invents a disagreement — the
old unconditional `|s|` append charge did exactly that. A reviewer should check
the charges before checking the invariants.

`Join` is the live undercharging hazard: `SumLen(parts) + |parts|` is *less*
than its measured cost, so a row whose output is one line per input item does
not get a proof yet. `171_82`, `89_463`, `2602_57` and `378_20` are each
provable except for this term. Every proof so far prints a single value.

Constants are free: the label is asymptotic, so `steps <= 7*n + 12` proves O(n).
Do not tune constants to look tight — take whatever the invariant supports.

## Logarithmic bounds

Dafny has no `log`. `solutions-nlogn/` proves the true O(n log n) for merge sort.
Two things make it work.

**Match the log's rounding to the code's rounding.** This is the general rule;
"use a ceiling log" is the merge-sort case of it.

```dafny
ghost function CeilLog2(n: nat): nat            // for a split on ceil(k/2)
  decreases n
{ if n <= 1 then 0 else 1 + CeilLog2((n + 1) / 2) }

ghost function Log2(x: nat): nat                // for a loop doing m := m / 2
  decreases x
{ if x <= 1 then 0 else 1 + Log2(x / 2) }
```

Merge sort recurses on `ceil(n/2)`; both halves of a split of size `k` are at
most `ceil(k/2)`, so `CeilLog2(ceil(k/2)) == CeilLog2(k) - 1` holds *by
definition*, and with floor-log that step is false at `k = 3`. A halving loop
rounds the other way, and there `Log2(m/2) == Log2(m) - 1` for `m >= 2` holds by
definition instead — `945_255` closes with no lemma at all. Pick the mismatched
one and the induction cannot close.

**Isolate every multiplication.** Z3 does not do nonlinear arithmetic. The whole
argument in one `calc` timed out at 30s. Splitting the two multiplication facts
into their own lemmas, so the solver never has to discover one, took it to 2.8s.

```dafny
lemma MulMonoRight(x: nat, p: nat, q: nat) requires p <= q ensures x * p <= x * q {}
lemma MulDistrib(a: nat, b: nat, k: nat, L: nat) requires a + b == k
  ensures a * L + b * L == k * L {}

lemma SortCostNLogN(k: nat) ensures SortCost(k) <= 2 * k * (CeilLog2(k) + 1) + 1
```

`solutions-verified/` retains the honest `O(n²)` fallback for the two original
sort rows and `solutions-nlogn/` carries their tight bound on a copy — an
artifact of the tight proof arriving second. A new sort row does not need that
split: `187_193` was written straight to the tight bound by reusing these
lemmas.

## Procedure

1. Copy the row from `solutions/` into `solutions-verified/<PID>/<SID>.dfy`.
   Never instrument in place — the ghost version is a second artifact.
2. Add `ghost steps: nat` to the out-params and an `ensures` naming the bound in
   terms of the input, matching the label's shape.
3. Charge every operation per the table. Loop invariants relate `steps` to the
   counter.
4. `dafny verify --solver-path /usr/local/bin/z3 --verification-time-limit 30`.
5. `python3 validate.py --solutions-dir solutions-verified --out-prefix ver_` —
   a bare `--only <SID>` resolves to `solutions/` and tests the ORIGINAL, and it
   overwrites the corpus-wide `data/validation.jsonl`. Then diff the emitted
   Python of the proof against its original: identical bytes is the real
   equivalence claim, and it is the only one available for a `loose` row.
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

31 rows in `solutions-verified/`, 2 in `solutions-nlogn/`. 33/33 verify, zero
`assume`. **`bigodafny/summaries/proof_obstructions.md` lists what is NOT
provable and why — read it before picking a row.** 164 rows are blocked on
`Join` alone; 19 on `decreases *`; 44 on unmeasured `set`/`map` costs. Behavioural equivalence is established by **emitted-Python identity**,
not by re-running tests — see the gate note below.

**`O(n*m)`: read the loop body, not the input shape.** Nine examined, seven
wrong, two right, and the split is mechanical. `3046_65` and `3091_384` walk
every token of every row, so a wider row costs more and the second dimension is
real. The six wrong ones touch a fixed number of positions per row (`row[0]`,
`row[1]`, up to `row[4]`) and never scan one — a row of width 1000 costs what a
row of width 2 costs, so there is no `m`. 39 rows still carry the label.
`1138_83` fails a third way: its `m` is a scalar modulus, not a size.

**`685_583` is an O(nlogn+mlogm) label on a row that never sorts** — two linear
max scans. Its sibling `685_777` carries O(n+m) for the same computation and is
right. Siblings computing the same thing should carry the same label; where they
do not, one is wrong and the pair is cheap to check.

**`1855_50` is an O(n**2) label on straight-line code** — no loop, no recursion
over a collection. First label proved wrong outside the O(n*m) family. The
O(n*m) cases name a dimension that does not vary; this one names a growth rate
nothing in the code has.

**Match the log's rounding to the code's rounding.** `945_255` halves by
rounding down and so wants a FLOOR log; merge sort splits on `ceil(k/2)` and
wants a ceiling one. With the matching log the key step holds by definition and
no lemma is needed. The old rule "use a ceiling log" was the special case.
`187_193` got the tight n log n bound on the first pass by reusing the
recursion-tree argument — the machinery is now cheap.

`827_148` has no polynomial bound at all until values are capped: its inner
catch-up loop is data-dependent. The proof takes the problem's stated
`1 <= d_i <= 1000` as a precondition and folds the cap into the constant. The
label assumes the same thing silently.

`1484_82`'s trailing comparison loop is bounded by total string length, not `n`,
so it is charged against `SumLen(numbers)`. That term is real work, not slack.

## The gates resolve to the wrong file

`validate.py` and `difftest.py` both scan `SOLUTIONS, INEXACT, UNVERIFIED,
VERIFIED` and take the **first** hit. A proved row exists in two places and
`solutions/` is scanned first, so a plain `validate.py --only <sid>` on a proved
row tests the **uninstrumented original**. `precheck.py` had this bug, was fixed
with `find_all()`, and the fix never reached the other two. Do not fix it here —
an agent may not edit a gate it is judged by. Instead:

- `python3 validate.py --solutions-dir solutions-verified --out-prefix ver_`
  points the existing flag at the instrumented copies.
- For `loose` rows, and as the stronger check generally, compare the **emitted
  Python** of the proof against its original. Byte-identical compiled code
  cannot differ on any input, and it re-confirms ghost erasure in the same step.
  A `loose` row will FAIL `validate.py` either way — that is the wrong gate for
  it, and its own Python fails the same comparison.

**`validate.py --only <ids>` overwrites `data/validation.jsonl`** with just
those rows, and `dataset.py` then reports 4 valid translations instead of 529.
Always pass `--out-prefix` on a partial run; it redirects the output file.
Restore from git if it happens.

## Charging: two measured corrections

`s := s + [x]` is **O(1)**, not O(|s|) — the Python backend builds a lazy
concat node. Reading `s[i]` between appends forces a flatten and *is* quadratic;
taking `|s|` is free. So charge 1 per append, and state the side condition that
the accumulator is not indexed inside the loop.

`Join` is **superlinear** (~L^1.2), so `SumLen + |parts|` undercharges it.
Rows whose output is one line per input item are therefore **deferred**, not
attempted: `171_82`, `89_463`, `2602_57`, `378_20`. Every proof so far prints a
single value. Fixing this — a linear-time join in the prelude, or a pinned-down
cost — unlocks that whole shape.
