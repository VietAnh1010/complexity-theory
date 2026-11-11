# Prove one row against its complexity label

Your directory is `{{DIR}}`. The prelude is at `../prelude.dfy` from there, and you may
read it. A hook denies every other path and enforces your budget.

**Label: `{{LABEL}}`.**

`row.dfy` holds the row's code, its Python as a comment, and a ghost counter `steps` that
is already charged. `proof.dfy` starts as a copy of `row.dfy`. Edit `proof.dfy` until it
proves an upper bound on `steps`. Read `proof.dfy` once before your first `Write` or `Edit`
of it: both tools fail on a file not read first.

```
dafny verify {{DIR}}/proof.dfy --verification-time-limit 30
```

Run exactly that command through Bash, with the Bash `timeout` set to 300000 and in the
foreground. No `cd`, pipes or other commands: the hook denies them.

## Budget

- **3 attempts.** Each run of the command above is one attempt. The hook denies a run on a
  `proof.dfy` that equals `row.dfy` or your last attempt.
- A **15-minute** clock from your first tool call guards against a runaway run.
- **A verified proof is not the end.** If a tighter bound may exist, keep trying until all 3
  attempts are used. Stop early only if your bound is in the label's class or below it.
- Past 15 minutes `result.json` is the only file left open: write it and stop.
- **Your job is to get the tightest proof you can. Work as diligently as you can.** Make every
  attempt a real proof attempt, and use what the verifier told you to improve the next one.
- **Never stop because a row looks hard or its cost looks above the label.** Prove the tightest
  bound the code supports.
- The hook blocks any other stop until you have used all 3 attempts or the clock has run out.
  A proof that does not verify is worth nothing, so report failure accurately.

## The bound

Add to `Solve` one top-level `ensures steps <= E`. `E` names only `Solve`'s inputs and
`|output|`. Constants do not matter: `steps <= 7*n + 12` proves O(n). Take whatever
constant the invariant supports.

**Keep every charge.** You may replace an `invariant` line with a different one. Every other
line of `row.dfy` stays in `proof.dfy`, in order, unchanged. Never move a line: put your own
lemma calls between the existing lines. Add only ghost state, `ensures`, `invariant`,
`decreases`, `assert`, ghost functions and lemmas. Give each helper the row calls its own
`steps` `ensures`.

## Rules you may not break

1. No `assume`, `{:verify false}`, `{:axiom}` or `{:only}`.
2. No `decreases *`: replace one in `row.dfy` with a real measure.
3. Never add or change a `requires` on the row's own methods and functions. If the bound
   seems to need one, try a bound that does not. If none verifies, record the row
   `unresolved` and name the clause. Your own ghost helpers may have their own `requires`.
4. The compiled Python must not change. Every helper you add is `ghost`. Name each local:
   no `_` wildcard. Do not reorder or restructure the row's statements.
5. If your proved bound exceeds the label, keep the proof and record it. An upper bound
   can confirm a label or fail to; it cannot refute one.

## Value versus size

A loop bounded by an input **value** counts: the value is a parameter of the bound. A
quantity fixed in the source is a constant.

## Output

Integer arithmetic costs `1`. Printing costs one step per character. Prove
`steps <= f(n) + c * |output|` and compare only `f(n)` with the label. The prelude links
charges to output:

```dafny
IntToStringDigits(x);   // |IntToString(x)| == Digits(x)
JoinLen(parts, sep);    // |Join(parts, sep)| == SumLen(parts) + (|parts| - 1) * |sep|
JoinIntsLen(xs, sep);   // |JoinInts(xs, sep)| == SumDigits(xs) + (|xs| - 1) * |sep|
```

## Sorts and binary searches: use the prelude

```dafny
SortCostWithin(|s|, n);          // SortCost(|s|) <= 2 * NLogN(n) + 1, any |s| <= n
ensures steps <= 2 * NLogN(n) + 5 * n + 3
```

A search loop over N elements:

```dafny
ghost var it: nat := 0;
while lo < hi
  invariant it + SearchPot(hi - lo) <= SearchPot(N)
{
  ghost var k := hi - lo;
  ...                              // lo := mid + 1 or hi := mid
  BisectStep(k, hi - lo);
  it := it + 1;
}
```

m searches, each costing `a` per halving plus `b`, fold with
`SearchLoopWithin(m, N, n, a, b)` into `a * NLogN(n) + b * n`. Carry the outer invariant
as `steps <= base + i * K` and step it with `CostMulDistrib(i, 1, i + 1, K)`.

`NLogN` is opaque: never `reveal NLogN()` in `Solve`, and never write the bound as
`2 * n * (CeilLog2(n) + 1)`.

For another logarithm, match the code's rounding. `CeilLog2` is in the prelude for a split
into ceil(k/2). For a loop doing `m := m / 2`, define a floor log yourself. Bound `Gcd` with
`GcdStepsBound`.

**Isolate every multiplication into its own lemma.** Z3 is bad at nonlinear arithmetic. The
prelude has `CostMulMono`, `CostMulMonoLeft`, `CostMulDistrib` and `CostMulAssoc`.

## Write back: `{{DIR}}/result.json`

```json
{"outcome": "proved",
 "best_attempt": 2,
 "stop_reason": "the bound is in the label's class, so I stopped",
 "bound": "3 * |a_list| + 4",
 "relation": "confirms",
 "relation_reason": "",
 "obstacle": null,
 "why_failed": null,
 "reads": [{"scope": "source", "target": "row.dfy", "reason": "call-graph"},
           {"scope": "prelude", "target": "IntToString", "reason": "cost"}]}
```

`outcome` is `proved` or `unresolved`. `proved` means at least one attempt verified.
`best_attempt` is the number of the tightest attempt that verified: that attempt is the proof
the audit checks, and `bound` is its bound. A later failed attempt does not lose it.

`stop_reason` says, in your own words, why you stopped where you did: what made you end the work,
and, if your bound is above the label, why you did not get a tighter one. Name what you tried and
what you did not try. Any honest answer is fine, including "I judged it not worth trying".

`relation`, for a proved row:

| value | when |
|---|---|
| `confirms` | the bound is in the label's class |
| `looser-slack` | above the label: you used a loose scaffold and did not reach the tight bound |
| `looser-structural` | above the label: the Python really pays a cost the label omits, usually a loop over an input value |
| `looser-costmodel` | above the label: the charges cost something more than CPython does |
| `looser-translation` | above the label: the Dafny does work the Python does not |
| `tighter-costmodel` | below the label: the charges cost something less than CPython does |
| `tighter-translation` | below the label: the Dafny does less work than the Python |
| `tighter-label` | below the label, and the Python itself does no more |

Every value except `confirms` needs a `relation_reason` naming the construct.

`obstacle`, for an unresolved row, names what blocked your last attempt:

| code | when |
|---|---|
| `z3-nonlinear` | Z3 will not prove a routine fact about products |
| `math-too-hard` | a needed fact about a function (a log, a square root, a sum) was not established |
| `invariant-gap` | a loop invariant is false or too weak: it lacks a simple fact about program state |
| `termination-not-proved` | nobody showed why a loop stops |
| `other` | none of these; `why_failed` must state the cause |

`why_failed` is one sentence: which invariant would not hold, or which multiplication the
solver would not do. Not "ran out of attempts".

`reads` lists, in order, the row and each helper or prelude declaration whose contract, cost
or termination you had to open. `scope` is `source`, `helper` or `prelude`; `reason` is
`call-graph`, `cost`, `contract`, `termination` or `bound`.

Final message: at most 3 lines. `result.json` is the record.
