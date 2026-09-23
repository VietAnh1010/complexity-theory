# `solutions-proved/` — the complexity label, machine-checked

305 files over 303 rows. All verify, none contains an `assume`;
`proofs.py` re-checks every one from scratch and records the result in
`data/complexity_proofs.jsonl`.

> Renamed from `solutions-verified/`. "Verified" is what `dafny verify` does,
> and that checks **safety** — indices, division, termination. These files
> check something else: that the row's **complexity label** is honest. The old
> name put them in a false pair with `solutions-unverified/`, which is about
> safety and always was.

## This is an overlay, not a status

Every other `solutions-*` directory is part of a partition: the 640 dataset
rows are split across `solutions/`, `solutions-unscreened/`,
`solutions-disputed/`, `solutions-unverified/` and `solutions-untranslated/`,
and each row is in exactly one.

This directory is different. Each file is an **instrumented copy** of a row
that also lives in one of those five:

| the row also lives in | rows |
|---|---|
| `solutions/` | 287 |
| `solutions-disputed/` | 15 |
| `solutions-unscreened/` | 1 |

15 proved rows sit against disputed rows, which is the point: a proved bound is
the strongest possible input to that review. `checkverdicts.py` enforces it —
an audit verdict that contradicts a machine-checked bound is rejected.

Consequence for any tool that walks the corpus: a row can exist in two places
at once, with **different preconditions**, because a proof is where a new
`requires` gets added to make a bound go through. `precheck.py`'s `find_all`
returns every copy for exactly this reason — `827_148` had two precondition
sets and only the weaker one was ever checked.

## `nlogn/`

    solutions-proved/nlogn/<problem_id>/<solution_id>.dfy

Two rows, `1484_82` and `603_284`. Their base proofs used to prove only a
quadratic bound, and these held the tight O(n log n) one beside them. Since
2026-09-23 the prelude carries a composable sort-cost bound and both base
proofs are tight, so **these two files duplicate them**: same preconditions,
same bound. They still verify. Removing the directory is pending a decision;
an automated delete was refused.

## `value-bounded/`

Proved rows whose bound names the MAGNITUDE of an input, not only how many
inputs there are. Its own README and MANIFEST.jsonl say what that means and
how a row leaves.

## Sorts and binary searches

The charge for a sort, `SortCost`, and its tight bound live in `prelude.dfy`
with a binary-search potential beside them (`SortCostNLogN`, `SortCostWithin`,
`SearchPot`, `BisectStep`, `SearchLoopWithin`). No proof here copies them any
more except `2188_359`, which keeps local opaque copies because its `Solve`
times out against the prelude's non-opaque `SortCost`.

## How a proof is written

`.claude/skills/bigodafny-prove/SKILL.md` has the procedure and the charging
convention. In outline: copy the row in, add a `ghost var steps` incremented at
every charged operation, state `ensures steps <= <bound>`, and prove it.

The charges come from `COMPLEXITY.md`, which under
`batches/cost-axioms/PLAN.md` **stipulates** collection costs rather than
measuring the Dafny Python backend. A proof written before that switch may
charge `|s|` for a `seq` update where the axioms now charge 1; the bound is
still sound, just no longer tight.

## Labels proved

    O(n*m) 9 · O(nlogn) 7 · O(n) 5 · O(n**2) 4 · O(n+m) 3
    O(1) 2 · O(n**2+m**2) 1 · O(nlogn+mlogm) 1 · O(logn) 1
