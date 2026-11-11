# Prove one row's time complexity

Your folder is `{{DIR}}`; the prelude is `{{PRELUDE}}`. A hook enforces these rules and your budget.

- Read, Grep: your folder and the prelude.
- Write, Edit: `proof.dfy` and `result.json`.
- Bash: only the command below, verbatim. No `cd`, `cat`, `cp`, `python` or pipes.

`row.dfy` holds the code, its Python as a comment, and a ghost counter `steps` that the code
already increments. `proof.dfy` starts as a copy of `row.dfy`. Read `proof.dfy` before your first
Write or Edit of it.

## Prove

```
dafny verify {{DIR}}/proof.dfy --verification-time-limit 30
```

Run it verbatim, in the foreground, Bash `timeout: 300000`.

- You have 3 attempts. Each run counts as one, even a run that fails to parse. The hook denies a
  run on an unchanged `proof.dfy`.
- You have 5 minutes. After that, you can write only `result.json`.
- Use all 3 attempts to tighten the bound, unless it is already in or below `class`. The hook
  blocks an earlier stop.

## The bound

Add one top-level `ensures steps <= E` to `Solve`; `E` names only `Solve`'s inputs and
`|output|`. Constants do not matter. A loop bounded by an input value makes that value a
parameter of `E`; a quantity fixed in the source is a constant.

- Every line of `row.dfy` stays, in order and unchanged, except `invariant` lines, which you may
  replace. Insert your lemma calls between the existing lines.
- Add only ghost state, `ensures`, `invariant`, `decreases`, `assert`, ghost functions and lemmas.
  Give each helper method the row calls its own `ensures` bounding its `steps`.
- No `assume`, `{:verify false}`, `{:axiom}`, `{:only}` or `decreases *` (give a real measure).
- Never add or change a `requires` on the row's code. If the bound needs one, record the row
  `unresolved` and name the clause. Your ghost helpers may have their own.
- The compiled Python must not change: helpers are `ghost`, no `_` locals, no reordering.

## Prelude

Printing costs one step per character, so prove `steps <= f + c * |output|` and compare only `f`
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
- For an outer loop, use `invariant steps <= base + i * K` and step it with
  `CostMulDistrib(i, 1, i + 1, K)`.
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
- `outcome` is `proved` when an attempt verified. `best_attempt` is the number of the tightest
  verified attempt, and `bound` is its `E`. The hook checks `outcome` and `best_attempt` against
  the verifier's results.
- `stop_reason`: why you stopped where you did. If the bound is above `class`, say what you tried
  and what you did not try.
- `relation`, for a proved row, compares the bound with `class`. Every value but `confirms` needs
  a `relation_reason` naming the construct.
  - `confirms`: the bound is in `class`.
  - Above `class`: `looser-slack` (your proof is looser than the code), `looser-structural` (the
    Python really pays the extra cost), `looser-costmodel` (the charges cost more than CPython),
    `looser-translation` (the Dafny does work the Python does not).
  - Below `class`: `tighter-costmodel` (the charges cost less than CPython), `tighter-translation`
    (the Dafny does less work than the Python), `tighter-label` (the Python itself does no more).
- `obstacle`, for an unresolved row, names what blocked the last attempt: `z3-nonlinear` (a product
  Z3 would not prove), `math-too-hard` (a fact about a log, root or sum), `invariant-gap` (a loop
  invariant too weak or false), `termination-not-proved`, or `other` (state the cause).
- `why_failed`: one sentence naming the invariant or product that failed, never "ran out of attempts".
- `reads`: each declaration you opened, in order. `scope` is `source`, `helper` or `prelude`;
  `reason` is `call-graph`, `cost`, `contract`, `termination` or `bound`.

Final message: at most 3 lines.

## Problem statement

{{STATEMENT}}
