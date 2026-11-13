# `prove-disputed-1`

Campaign 5 of 9 to prove every unproved row, and the first drawn from `solutions-disputed/`: 20 of
its 186 unproved, gate-passing rows (`sample.py --dir solutions-disputed`, seed `20261113`, no
`--exclude-drawn`). Three Sonnet agents, 3 attempts and 5 minutes per row. Each brief is the
`bigodafny-prove-campaign` skill's `PROMPT.md` followed by its `PROMPT_disputed.md`: prove the
tightest upper bound you can, with the label and the audit's guess as hints. The proved class is
meant to become the row's `truth`.

This is not a measurement of label-proving and stays out of `prove_stats.py`.

**Result: 20 proved, 0 unresolved.** Every row closed within its time budget.

The sampler excluded `1950_45` and `1950_47`: no test gate (`unvalidatable`).

## Relations to the stated label

| relation | rows |
|---|---:|
| `tighter-label` | 7 |
| `looser-structural` | 7 |
| `tighter-translation` | 3 |
| `confirms` | 3 |

`label_relation.jsonl` keeps the agents' relations (`review: bound-only`); the main agent did not
re-read each Python.

## Rows whose proof cannot become `truth`

The Dafny drops work the Python does, so the proof bounds the wrong program. Under the plan's
rule these get their translation fixed, not their label changed:

| row | label | proved | what the Dafny drops |
|---|---|---|---|
| `1099_169` | `O(nlogn)` | `O(n)` | the Python's `a.sort()`; the Dafny counts distinct values with a set |
| `1054_212` | `O(nlogn)` | `O(n)` | the Python sorts the tokens before its `Counter` |
| `101_43` | `O(n+m)` | `O(n)` | `Solve` receives `b` parsed and reads only `b_list[0]`; the `m` term is parsing |

## Value-bounded

`310_121` (trial division up to the value), `1364_163` (bit length of the values) and `281_250`
(Euclid's depth) are `looser-structural` with a reason naming an input value. Their proofs moved
to `solutions-proved/value-bounded/` with the include fixed and re-verified.

## Fixed by the main agent before promotion

`3005_13` declared a non-ghost temporary `line`, so its emitted Python differed from the row's.
It became `ghost var line`, and the row's original expression went back into the compiled
assignment. `1338_48` dropped the row's bare `{ ... }` block around `Solve`'s body; the block is
back. `619_362` guarded two proof-only lemma calls with `if (forall ...)`, which compiles; the
guards are now `ghost var`s. All three re-verify. Agent `b` changed the word "assumes" to "presumes" in the review header comment of
4 proof copies; comments do not reach the emitted Python.

## Effort

| attempts used | rows |
|---|---:|
| 1 | 14 |
| 2 | 5 |
| 3 | 1 |
