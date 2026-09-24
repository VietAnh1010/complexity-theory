# Campaign 7 rerun — a fresh, bounded proof attempt per row

Your rows are in `batches/prove-sample-7/rerun/slice_r{{SLICE}}.jsonl`. Each line
gives the solution id, its source path under `solutions/`, and its label.

This is a **real retry**. Earlier attempts on these rows exist; you must not
look at them, and your result must stand on its own.

## Read first, in this order

1. `bigodafny/DOCS.md`
2. `bigodafny/COMPLEXITY.md`
3. `bigodafny/batches/prove-sample-7/README.md`
4. `bigodafny/batches/prove-sample-7/PROMPT_a.md` — the campaign brief: charges,
   the ghost-counter shape, the hard rules, the budget, the trajectory schema,
   the reading trace. **Everything in it applies except the overrides below.**
5. For each row, its source file in `solutions/`.

## Overrides to PROMPT_a.md

**Where your proof goes.** Not `solutions-proved/`. Write your instrumented copy to

    bigodafny/batches/prove-sample-7/rerun/<pid>/<sid>.dfy

and fix its include to `include "../../../../prelude.dfy"`. Verify it there:

    cd /home/user/complexity-theory/bigodafny
    export PATH="$PATH:/root/.dotnet/tools"
    dafny verify batches/prove-sample-7/rerun/<pid>/<sid>.dfy --solver-path /usr/local/bin/z3 --verification-time-limit 30

**Where your record goes.** Append one JSON object per line to

    bigodafny/batches/prove-sample-7/rerun/traj_rerun_{{SLICE}}.jsonl

as soon as each row is finished, not at the end. Same schema as PROMPT_a.md,
including `reads`. Write to no other file in `batches/`.

**Out of budget or unproved.** Delete only your own
`batches/prove-sample-7/rerun/<pid>/<sid>.dfy`, record `unresolved` with the
concrete obstruction, move on.

## Do not read — this is what makes the retry fresh

- Anything under `bigodafny/solutions-proved/<pid>/` or
  `bigodafny/solutions-proved/value-bounded/<pid>/` for any `<pid>` in your
  slice — the target row's existing proof and any other solution of the same
  problem.
- `batches/prove-sample-7/traj_*.jsonl`, `audit.jsonl`, `old_record.jsonl`,
  `label_relation.jsonl`, `obstacles.jsonl`, `summary.json`.
- Any other campaign's records under `batches/prove-sample*/`, and `data/`.
- Another rerun agent's `traj_rerun_*.jsonl` or `rerun/<pid>/` files.

If you find yourself about to open one of these, don't. A proof that exists
elsewhere must not influence yours.

## Never modify

`solutions/`, `solutions-proved/`, `prelude.dfy`, `data/`, any manifest, slice
or prompt, or `validate.py`, `difftest.py`, `verify_all.py`, `precheck.py`,
`proofs.py`.

## Record `proved` only for a proof you built in this retry and verified

The `reads` array is required and must be truthful: first the source row
(`scope: "source"`, `reason: "call-graph"`), then only the helpers or prelude
declarations you actually inspected for their implementation, contract,
termination or cost.

## Reporting

No preamble, no per-command narration. Final message at most 8 lines: counts
proved / unresolved, any `relation` that is not `confirms`, and the most common
obstacle.
