# BigODafny operating rules

Read `DOCS.md` first. This file is the short list of rules that apply whenever
you edit a translation, proof, label verdict, or status record.

## Preserve the algorithm

The row's complexity label belongs to the original Python solution, not merely
to its input/output behaviour. A different algorithm can pass every test and
still make the row's label false. You may restructure code within the same
complexity class when necessary for Dafny; do not replace sort with max, a
quadratic scan with a closed form, or one sibling solution with another.

## Respect the status directories

The six `solutions*` status directories partition the corpus. Move a row only
when the directory's README says its entry and exit conditions are met.
`solutions-proved/` is an overlay: copy a row there to add ghost proof state;
do not remove its source copy.

## Use the right gate

- Strict rows use `validate.py`; loose rows use `difftest.py --loose`.
- A passing test gate is behavioural evidence, not a safety or complexity proof.
- Use `precheck.py` whenever a proof or verification fix adds `requires`.
- Use `proofs.py` for instrumented complexity proofs.
- Never weaken a gate to make the row under review pass.

## Proof restrictions

Proof changes may add ghost state, lemmas, `ensures`, invariants, decreases
clauses, and verified preconditions. They must not change executable behaviour.

- No `assume` in `solutions-proved/`.
- No `decreases *` in a complexity proof.
- Do not silently narrow a row's contract. Check every new precondition against
  real inputs.
- A proved upper bound can confirm a label or show that it is too loose. It
  cannot show that the program is slower than the label; that needs a lower
  bound.

## Cost model

Use `COMPLEXITY.md`, not historical measurements. The project charges standard
asymptotic collection costs by stipulation. In particular, a functional Dafny
sequence update is O(1) in the model even though the current Python backend may
copy. An input value used as a loop bound is a parameter of the cost, even when
the contest statement caps it.

## Record work honestly

An unresolved row is useful data. Record the concrete obstacle: a missing
invariant, nonlinear arithmetic, an unavailable termination measure, or an
unrelated value parameter. Do not write "ran out of time" when the actual
problem is known.

For proof campaigns, trajectory records are append-only evidence. Do not edit
old attempts to make the history look cleaner. Use the current campaign schema,
including `reads` where required.

**Keep every proof attempt, including failed ones.** Each attempt's `.dfy` is
saved to `batches/<campaign>/attempts/<pid>/<sid>.<n>.dfy` and never deleted.
Only `solutions-proved/` is limited to verified proofs.

## Shared outputs

Subset commands can overwrite shared JSONL. Use their dedicated partial-output
mode when available, and inspect the resulting row count before replacing a
corpus-wide record. `batches/README.md` documents known failures of this kind.

## Toolchain

The reproducibility target is Dafny 4.11.0 with Z3 4.12.1. Keep the version
fixed for corpus-wide checks unless the task is explicitly a toolchain upgrade.
