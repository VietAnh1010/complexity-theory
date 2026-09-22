---
name: bigodafny-prove
description: Prove a BigOBench row's time-complexity label in Dafny with a ghost step counter. Use when asked to prove, establish, or machine-check a complexity label, when working in solutions-proved/ or solutions-proved/nlogn/, or when a label is suspected wrong. Covers the charging convention and the CeilLog2 recursion-tree argument.
---

# Proving the complexity label

Read the `bigodafny` skill first, and `bigodafny/COMPLEXITY.md` for the full
convention — this is the operating procedure, that is the contract.

`solutions/` proves **behaviour**: the Dafny reproduces the Python's stdout.
It says nothing about the label. `solutions-proved/` proves the **label**.

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

**`bigodafny/COMPLEXITY.md` § 1 is the authority; this is the summary.** The
charges are **stipulated**, not read off Dafny's Python backend — the labels
were measured on CPython, so a backend-derived model compared two unrelated
implementations.

Charge 1 per: `int` arithmetic and comparison, `s[i]`, `|s|`, one unit of loop
overhead per iteration, and every collection operation CPython does in constant
time.

| operation | charge |
|---|---|
| `s[i := v]`, `s + [x]`, `s[a..b]` | `1` |
| `m[k := v]`, `m[k]`, `k in m`, `\|m\|` | `1` |
| `x in s`, `s + {x}` on a set | `1` |
| `s + t` (concat) | `\|t\|` |
| `m.Keys`, `m.Values`, `m.Items` | `\|m\|` |
| `multiset(s)` | `\|s\|` |
| `multiset(a) == multiset(b)` | `\|a\|+\|b\|` |
| `Join(parts, sep)` | `SumLen(parts) + \|parts\|` |
| a recursive prelude function over a seq or string | its length |
| a helper call | the helper's own `steps` |

**The 33 existing proofs predate this.** Several charge `|s|` where the table now
charges `1`, so their bounds are sound but not tight, and a couple prove a
quadratic the axioms would let you prove linear. Re-read a proof's charges before
citing its bound as evidence about a label.

**Miscounting here is the entire risk, and it runs both ways.** Undercharging
turns a real O(n²) into a proved "O(n)" and Dafny still says verified.
Overcharging puts a correct label out of reach and invents a disagreement — the
old unconditional `|s|` append charge did exactly that. A reviewer should check
the charges before checking the invariants.

**Measure against a control, never against a ratio of 2.0.** `Join` was called
superlinear here on ratios of ~2.2 per doubling. A known-linear control in the
same harness gives 2.40/2.32/2.24 — higher. The excess was constant overhead.
That call blocked 164 rows and sent four agent runs to a decline they did not
need, and refusing to charge an operation felt like the safe choice while it was
happening. It is not: an overcharge invents a false obstruction exactly as an
undercharge invents a false bound. `171_82`, `89_463`, `2602_57` and `378_20`
are provable and are where a next wave should start.

Constants are free: the label is asymptotic, so `steps <= 7*n + 12` proves O(n).
Do not tune constants to look tight — take whatever the invariant supports.

## Logarithmic bounds

Dafny has no `log`. `solutions-proved/nlogn/` proves the true O(n log n) for merge sort.
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

`solutions-proved/` retains the honest `O(n²)` fallback for the two original
sort rows and `solutions-proved/nlogn/` carries their tight bound on a copy — an
artifact of the tight proof arriving second. A new sort row does not need that
split: `187_193` was written straight to the tight bound by reusing these
lemmas.

## Procedure

1. Copy the row from `solutions/` into `solutions-proved/<PID>/<SID>.dfy`.
   Never instrument in place — the ghost version is a second artifact.
2. Add `ghost steps: nat` to the out-params and an `ensures` naming the bound in
   terms of the input, matching the label's shape.
3. Charge every operation per the table. Loop invariants relate `steps` to the
   counter.
4. `dafny verify --solver-path /usr/local/bin/z3 --verification-time-limit 30`.
5. `python3 validate.py --solutions-dir solutions-proved --out-prefix ver_` —
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

**"Agrees with the label" means consistent, not tight.** `5_100` is proved
`2n+3` against an O(n) label, and its loop is really Θ(√n): `m -= k; k += 1`
decreases m by 1+2+3+…. `1011_368` is the same story. Both proofs are sound and
both labels are loose. Before recording agreement, ask whether the bound is
tight -- a loose upper bound hides a mislabel.

**Does not claim**: that `steps` is wall-clock time. The bound is only as honest
as the charging convention.

**Against the label**: BigOBench's label is synthetic — regression over profiling
runs. Where a proof and the label disagree, **the proof is the stronger
statement. Record the disagreement; never adjust the proof to match the label.**

## Results so far

31 rows in `solutions-proved/`, 2 in `solutions-proved/nlogn/`. 33/33 verify, zero
`assume`. **`bigodafny/summaries/proof_obstructions.md` lists what is NOT
provable and why — read it before picking a row.** 164 rows are blocked on
`decreases *` (19 rows) and unmeasured `set`/`map` costs (44). Behavioural equivalence is established by **emitted-Python identity**,
not by re-running tests — see the gate note below.

**`O(n*m)`: read the loop body, not the input shape.** Nine examined, seven
wrong, two right, and the split is mechanical. `3046_65` and `3091_384` walk
every token of every row, so a wider row costs more and the second dimension is
real. The six wrong ones touch a fixed number of positions per row (`row[0]`,
`row[1]`, up to `row[4]`) and never scan one — a row of width 1000 costs what a
row of width 2 costs, so there is no `m`. 39 rows still carry the label.
`1138_83` fails a third way: its `m` is a scalar modulus, not a size.

**`685_583` was recorded here as a disproved label. It is not one** -- its
Python sorts both lists, so O(nlogn+mlogm) is correct and the DAFNY dropped the
sort. The proved bound was sound; the conclusion drawn from it was not, because
it was read off the Dafny without opening the Python.

**A sibling disagreement means read both Pythons, not that a label is wrong.**
`685_777` computes the same answer without sorting and is correctly O(n+m).
Inferring from that that one of the two labels must be wrong is backwards: two
rows of one problem are kept because they differ, and here they differ by
sorting. Same trap in reverse on `396_361`, where an auditor called a genuine
label error a translation error -- the Python's `max(dimensions[i])` runs over a
rectangle's two numbers, so it is O(1) per row and the O(n*m) label really is
wrong.

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

- `python3 validate.py --solutions-dir solutions-proved --out-prefix ver_`
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

## Charging: the correction that cost the most

`Join` is **linear**, `SumLen(parts) + |parts|`. The opposite was recorded
first, from ratios read without a control, and it blocked 164 rows for a
session. Per-line output is not blocked; `171_82`, `89_463`, `2602_57` and
`378_20` are the best next targets.

The append side condition is gone with the axioms — `s + [x]` is charged `1`
unconditionally now, so a proof no longer has to state that the accumulator is
not indexed inside the loop. That condition was about the backend's lazy concat
node, and the backend is no longer what the charges describe.

## When the bound carries an input value

If your proved bound depends on the MAGNITUDE of an input rather than on how
many inputs there are, the row is `looser-structural`, not `confirms`, and it
belongs in `solutions-proved/value-bounded/`. Read that directory's README
before deciding; it has the procedure, the manifest format, and the three ways
a row leaves.

`prelude.dfy`'s `Sort` proves `SortIsPermutation` and nothing about order, so
no proof can currently say "the last element after sorting is the maximum". If
a bound needs that, say so and stop — do not work around it with an `assume`.
