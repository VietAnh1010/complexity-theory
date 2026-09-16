# `solutions-proved/` — the complexity label, machine-checked

33 files: 31 base proofs plus 2 tight-bound variants under `nlogn/`. All 33
verify, none contains an `assume`.

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

| the row also lives in | proofs |
|---|---|
| `solutions/` | 18 |
| `solutions-disputed/` | 12 |
| `solutions-unscreened/` | 1 |

Twelve proofs sit against disputed rows, which is the point: a proved bound is
the strongest possible input to that review. `checkverdicts.py` enforces it —
an audit verdict that contradicts a machine-checked bound is rejected.

Consequence for any tool that walks the corpus: a row can exist in two places
at once, with **different preconditions**, because a proof is where a new
`requires` gets added to make a bound go through. `precheck.py`'s `find_all`
returns every copy for exactly this reason — `827_148` had two precondition
sets and only the weaker one was ever checked.

## `nlogn/`

    solutions-proved/nlogn/<problem_id>/<solution_id>.dfy

Two rows, `1484_82` and `603_284`, whose merge sort is genuinely O(n log n).
Dafny has no `log`, so the tight bound needs a `CeilLog2` recursion-tree
argument; the simpler quadratic fallback survives at
`solutions-proved/<pid>/<sid>.dfy` alongside it. This is a **variant of a
proof**, not a status of its own, which is why it nests here instead of sitting
beside the partition.

> Merged in from a top-level `solutions-nlogn/`. One `rglob` over
> `solutions-proved/` reaches both, and `proofs.py` records which is which in
> `proof_variant` (`base` or `nlogn`) in `data/complexity_proofs.jsonl`.

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
