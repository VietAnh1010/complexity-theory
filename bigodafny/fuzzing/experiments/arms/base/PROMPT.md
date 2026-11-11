# State and prove one row's time complexity

Your folder is `{{DIR}}`; the prelude is `{{PRELUDE}}`. A hook enforces these rules and your budget.

- Read, Grep: your folder and the prelude.
- Write, Edit: `proof.dfy` and `result.json`.
- Bash: only the command below, verbatim. No `cd`, `cat`, `cp`, `python` or pipes.

`row.dfy` holds the code, its Python as a comment, and a ghost counter `steps` that the code
already increments. `proof.dfy` starts as a copy of `row.dfy`.

**Task:** state the tightest time-complexity class of `Solve` in its input sizes and values,
ignoring the statement's upper limits on them, and prove an upper bound on `steps` in
`proof.dfy`. Work however you like.

## Verifying

```
dafny verify {{DIR}}/proof.dfy --verification-time-limit 30
```

Run it verbatim, in the foreground, Bash `timeout: 300000`. You have 3 attempts and 5 minutes.
Each run counts as one attempt, even a run that fails to parse. The hook denies a run on an
unchanged `proof.dfy`.

## What counts as a proof

- `Solve` has one top-level `ensures steps <= E`, where `E` names only `Solve`'s inputs and
  `|output|`.
- Every line of `row.dfy` stays in `proof.dfy`, in order and unchanged, except `invariant` lines,
  which you may replace. Add only ghost state, `ensures`, `invariant`, `decreases`, `assert`,
  ghost functions and lemmas.
- No `assume`, `{:verify false}`, `{:axiom}`, `{:only}` or `decreases *`.
- No added or changed `requires` on the row's own methods and functions. Your own ghost helpers
  may have their own.
- The compiled Python must not change: every helper you add is `ghost`, and no local is named `_`.

## Write back: `{{DIR}}/result.json`

```json
{"outcome": "proved",
 "class": "O(n)",
 "best_attempt": 2,
 "bound": "3 * |a_list| + 4",
 "stop_reason": "why you stopped where you did"}
```

- `outcome` is `proved` (an attempt verified) or `unresolved`.
- `class` is the class of `E` without its `|output|` term. Write it with no spaces, like `O(1)`,
  `O(logn)`, `O(n)`, `O(nlogn)`, `O(n**2)`, `O(n**1.5)`, `O(n*m)`, `O(n+mlogm)`: powers take `**`,
  products `*`, and `log` follows its factor with no `*` or brackets. The hook blocks your stop
  until `class` has this form.
- `best_attempt` is the number of a verified attempt you stand by, and `bound` is its `E`. The
  hook checks `outcome` and `best_attempt` against the verifier's results.

## Problem statement

{{STATEMENT}}
