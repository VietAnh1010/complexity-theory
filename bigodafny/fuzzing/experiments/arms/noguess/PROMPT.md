# Prove one row's time complexity

Directory: `{{DIR}}`. Prelude: `{{PRELUDE}}`, readable. A hook denies every other path and
enforces the budget.

- Read, Grep: this directory and the prelude.
- Write, Edit: `proof.dfy` and `result.json`.
- Bash: only the command below, verbatim. No `cd`, `cat`, `cp`, `python` or pipes.

`row.dfy` holds the code, its Python as a comment, and a charged ghost counter `steps`.
`proof.dfy` starts as a copy. Read `proof.dfy` before your first Write or Edit of it.

## Prove

```
dafny verify {{DIR}}/proof.dfy --verification-time-limit 30
```

Run it verbatim, in the foreground, Bash `timeout: 300000`.

- 3 attempts. Every run is one, a parse error included. A run on an unchanged `proof.dfy` is denied.
- A 5-minute clock; after it only `result.json` is writable.
- Use all 3 attempts to tighten the bound unless it is in or below `class`; the hook blocks an
  earlier stop.

## The bound

Add one top-level `ensures steps <= E` to `Solve`; `E` names only `Solve`'s inputs and
`|output|`. Constants do not matter. A loop bounded by an input value makes that value a
parameter of `E`; a quantity fixed in the source is a constant.

- Every line of `row.dfy` stays, in order and unchanged, except `invariant` lines, which you may
  replace. Put lemma calls between lines.
- Add only ghost state, `ensures`, `invariant`, `decreases`, `assert`, ghost functions and lemmas.
  Give each helper the row calls its own `steps` `ensures`.
- No `assume`, `{:verify false}`, `{:axiom}`, `{:only}` or `decreases *` (give a real measure).
- Never add or change a `requires` on the row's code. If the bound needs one, record the row
  `unresolved` and name the clause. Your ghost helpers may have their own.
- The compiled Python must not change: helpers are `ghost`, no `_` locals, no reordering.

## Prelude

Printing costs one step per character: prove `steps <= f + c * |output|`, and compare only `f`
with `class`.

```dafny
IntToStringDigits(x);     // |IntToString(x)| == Digits(x)
JoinLen(parts, sep);      // |Join(parts, sep)| == SumLen(parts) + (|parts| - 1) * |sep|
JoinIntsLen(xs, sep);     // |JoinInts(xs, sep)| == SumDigits(xs) + (|xs| - 1) * |sep|
SortCostWithin(|s|, n);   // SortCost(|s|) <= 2 * NLogN(n) + 1, any |s| <= n
```

- `NLogN` is opaque: never reveal it or write it out as `CeilLog2`.
- Binary search over N: a ghost `it` with `invariant it + SearchPot(hi - lo) <= SearchPot(N)`,
  and `BisectStep(k, hi - lo)` after each halving, `k` being `hi - lo` before it.
  `SearchLoopWithin(m, N, n, a, b)` folds m searches into `a * NLogN(n) + b * n`.
- Outer loops: `invariant steps <= base + i * K`, stepped by `CostMulDistrib(i, 1, i + 1, K)`.
- Logs: `CeilLog2` for ceil splits; your own floor log for `m := m / 2`; `GcdStepsBound` for `Gcd`.
- Z3 is bad at products: put each multiplication in a lemma, using `CostMulMono`,
  `CostMulMonoLeft`, `CostMulDistrib` and `CostMulAssoc`.

## `{{DIR}}/result.json`

```json
{"outcome": "proved", "class": "O(n)", "best_attempt": 2, "bound": "3 * |a_list| + 4",
 "stop_reason": "the bound is in my class, so I stopped",
 "relation": "confirms", "relation_reason": "", "obstacle": null, "why_failed": null,
 "reads": [{"scope": "source", "target": "row.dfy", "reason": "call-graph"}]}
```

- `class`: the tightest time-complexity class of `Solve` in its input sizes and values, ignoring
  the statement's upper limits on them. No spaces, like `O(1)`, `O(logn)`, `O(nlogn)`,
  `O(n**2)`, `O(n**1.5)`, `O(n*m)`, `O(n+mlogm)`. Main measure `n`, second `m`.
- `outcome` is `proved` when an attempt verified. `best_attempt` is the tightest verified attempt,
  and `bound` its `E`. The hook checks both against the verifier.
- `stop_reason`: why you stopped there; if the bound is above `class`, what you tried and did not.
- `relation`, for a proved row, the bound against `class`: `confirms` (in it); above it,
  `looser-slack` (loose scaffold), `looser-structural` (the Python pays it), `looser-costmodel`
  (charges exceed CPython), `looser-translation` (the Dafny does extra work); below it,
  `tighter-costmodel`, `tighter-translation`, `tighter-label` (the Python does no more).
  Every value but `confirms` needs `relation_reason`.
- `obstacle`, for an unresolved row, what blocked the last attempt: `z3-nonlinear`,
  `math-too-hard`, `invariant-gap`, `termination-not-proved`, or `other` (state the cause).
  `why_failed`: one sentence naming the invariant or product, never "ran out of attempts".
- `reads`: each declaration you opened, in order. `scope` is `source`, `helper` or `prelude`;
  `reason` is `call-graph`, `cost`, `contract`, `termination` or `bound`.

Final message: at most 3 lines.

## Problem statement

{{STATEMENT}}
