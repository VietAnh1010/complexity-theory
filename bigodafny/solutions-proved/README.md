# `solutions-proved/` — the complexity label, machine-checked

321 files, one per row. All verify, none contains an `assume`;
`proofs.py` re-checks every one from scratch and records the result in
`data/complexity_proofs.jsonl`.

"Proved", not "verified": `dafny verify` checks **safety** (indices, division,
termination), and `solutions-unverified/` is about safety. These files check
that the row's **complexity label** is honest.

## This is an overlay, not a status

Every other `solutions-*` directory is part of a partition: the 640 dataset
rows are split across `solutions/`, `solutions-unscreened/`,
`solutions-disputed/`, `solutions-unverified/` and `solutions-untranslated/`,
and each row is in exactly one.

This directory is different. Each file is an **instrumented copy** of a row
that also lives in one of those five:

| the row also lives in | rows |
|---|---|
| `solutions/` | 264 |
| `solutions-disputed/` | 52 |
| `solutions-unsure/` | 4 |
| `solutions-unscreened/` | 1 |

52 proved rows sit against disputed rows, which is the point: a proved bound is
the strongest possible input to that review. `checkverdicts.py` enforces it —
an audit verdict that contradicts a machine-checked bound is rejected.

Consequence for any tool that walks the corpus: a row can exist in two places
at once, with **different preconditions**, because a proof is where a new
`requires` gets added to make a bound go through. `precheck.py`'s `find_all`
returns every copy for exactly this reason — `827_148` had two precondition
sets and only the weaker one was ever checked.

## `value-bounded/`

Proved rows whose bound names the MAGNITUDE of an input, not only how many
inputs there are. Its own README and MANIFEST.jsonl say what that means and
how a row leaves.

## Sorts and binary searches

The charge for a sort, `SortCost`, and its tight bound live in `prelude.dfy`
with a binary-search potential beside them (`SortCostNLogN`, `SortCostWithin`,
`SearchPot`, `BisectStep`, `SearchLoopWithin`). No proof here copies them
except `2188_359`, which keeps local opaque copies because its `Solve`
times out against the prelude's non-opaque `SortCost`.

## How a proof is written

`.claude/skills/bigodafny-prove/SKILL.md` has the procedure and the charging
convention. In outline: copy the row in, add a `ghost var steps` incremented at
every charged operation, state `ensures steps <= <bound>`, and prove it.

The charges come from `COMPLEXITY.md`, which **stipulates** collection costs
rather than measuring the Dafny Python backend. Some proofs still charge `|s|`
for a `seq` update where the model charges 1; the bound is sound, just not
tight.

## Same code as the row

A proof may add only ghost code: the proof and its row must compile to the same
Python. The campaign `audit.py` checks this for every drawn row. `2496_30`
(caps added to three loop conditions) still differs and is under review.

A proof never adds or changes a `requires` on the row's own code; a needed
precondition goes into the row first. `audit.py` checks this too.

## Labels proved

    O(n) 150 · O(nlogn) 68 · O(n**2) 40 · O(1) 32 · O(n+m) 14 · O(n*m) 11
    O(nlogn+mlogm) 4 · O(logn) 2 · O(n+m)log(n+m) 1 · O(n**2+m**2) 1

## Current scope

The overlay has 321 proof files. The relation to the label is recorded beside
each row in the campaign records; a proof may confirm the label, expose a
structural cost the label omits, or be tighter for a documented model reason.
