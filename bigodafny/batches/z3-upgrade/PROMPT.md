# Make a proof verify again under Z3 5.1.0

Your rows are listed in `batches/z3-upgrade/slice_{{SLICE}}.jsonl`. Each names
a proof in `solutions-proved/` that verified under the old toolchain and now
times out under Dafny 4.11.0 with Z3 5.1.0. The proof's argument is believed
sound; the solver no longer finds it in time. You make it verify again.

## What you may change

Proof text only: `assert`s, lemma calls, new ghost lemmas and functions,
`{:isolate_assertions}`, `{:opaque}` / `reveal` on ghost functions you add,
invariants, `decreases`, splitting a long `ensures` argument into lemmas.

**Keep the charges and the bound.** Every `steps` update and the `ensures`
bound stay as they are. If the bound cannot be proved as stated, you may prove
a looser one in the same class; never a different class.

Executable code stays byte-identical: the audit compiles your file and the
original row to Python and compares them. No `assume`, no `decreases *`, never
add or change a `requires`. Some proofs already carry a `requires` their row
lacks; leave it exactly as it is.

What usually works under a new solver:

- `{:isolate_assertions}` on the method that times out, to find which
  obligation is slow.
- Every product in its own lemma: `CostMulMono`, `CostMulMonoLeft`,
  `CostMulDistrib`, `CostMulAssoc` in the prelude.
- An opaque atom for a nonlinear term the solver keeps expanding.

## Per row

1. Read the proof (`proof` in the slice line). Do not edit it.
2. Copy it to `<attempt_dir>/<sid>.1.dfy` with
   `include "../../../../prelude.dfy"`.
3. `timeout 300 dafny verify <file>` as its own command, with **no**
   time-limit flag: that is how the `proofs.py` gate runs it. Find what times
   out, change it, save the next attempt as `<sid>.<n+1>.dfy`. Never overwrite
   or delete an attempt.

Do not touch `solutions*/`, `prelude.dfy`, `proofs.py`, `data/`, or another
row's files. Do not read `batches/` beyond your slice and this brief.

## Budget — hard

Work **one row at a time**, and run one `dafny` at a time: parallel runs load
the machine, and a loaded machine turns borderline proofs into timeouts.

3 attempts and 8 minutes per row from your first command on it. Run
`date +%s` at the start and end of each row.

## What to write back

Append one line per row to `batches/z3-upgrade/traj_{{SLICE}}.jsonl` as soon as
it finishes:

```json
{"solution_id":"2425_5","label":"O(nlogn)","outcome":"repaired",
 "old_bound":"…","new_bound":"…","slow":"the final ensures in Solve",
 "change":"isolated the n*K product into MulBound; {:isolate_assertions} on Solve",
 "attempts":[{"n":1,"outcome":"timeout","note":"…","file":"2425_5.1.dfy"}],
 "seconds":210,"why_failed":null,"obstacle":null}
```

`outcome` is `repaired` or `unresolved`. On `unresolved`, `obstacle` is
`z3-nonlinear`, `invariant-gap` or `budget`, and `why_failed` names the
obligation that would not close. `seconds` comes from `date +%s`.

Final message ≤ 6 lines: per row, outcome and what was slow.
