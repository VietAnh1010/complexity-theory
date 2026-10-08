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

The seven `solutions*` status directories partition the corpus. Move a row only
when the directory's README says its entry and exit conditions are met.
`solutions-proved/` is an overlay: copy a row there to add ghost proof state;
do not remove its source copy.

## Use the right gate

- Strict rows use `validate.py`; loose rows use `difftest.py --loose`.
- A passing test gate is behavioural evidence, not a safety or complexity proof.
- Use `precheck.py` whenever a verification fix adds `requires`.
- Use `proofs.py` for instrumented complexity proofs.
- Never weaken a gate to make the row under review pass.

## Proof restrictions

Proof changes may add ghost state, lemmas, `ensures`, invariants, and decreases
clauses. They must not change executable behaviour.

- **A proof never adds or changes a `requires` on the row's own methods and
  functions.** If a precondition is needed, add it to the row in its own
  directory, re-run that row's gates and `precheck.py`, then copy it into the
  proof. Ghost helpers the proof adds may have their own `requires`.

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

**Keep every proof attempt that differs from the promoted proof.** Each
attempt's `.dfy` is saved to `batches/<campaign>/attempts/<pid>/<sid>.<n>.dfy`
during the run, failed ones included. After the audit and promotion, delete
only the attempt identical (ignoring the `include` line) to the proof now in
`solutions-proved/`, and point the audit's `final` field at that proof. Only
`solutions-proved/` is limited to verified proofs.

## Write documentation in the present tense

State documents (`DOCS.md`, `COMPLEXITY.md`, this file, the `solutions*/README.md`
files, the skills) say what is true now. No "renamed from", "since <date>",
"N rows arrived on <date>", or "an earlier version said". When something
changes, update the state document in place and add one dated bullet to
`CHANGELOG.md`. A campaign's run record belongs in `batches/<campaign>/README.md`;
superseded data lines belong in `old-record.jsonl`.

## Delete one-off scripts when the task is done

A script written for one migration, campaign or repair (sampling, slicing,
promoting, normalizing, slimming transcripts) is deleted before the work is
committed. It encodes the corpus as it was that day and will not run correctly
once the corpus moves on, so keeping it "for reproducibility" reproduces
nothing. Record what it did in the batch README, in prose. Keep its outputs
only if a record needs them; do not leave per-slice inputs or scratch files
behind. Only tools the project runs again belong in the tree.

Generated files that no script reads back (summaries, dashboard payloads,
scratch output) go to `out/`, which is git-ignored (`common.OUT`). `data/`
holds only records that a script or a person reads.

## Shared outputs

Subset commands can overwrite shared JSONL. Use their dedicated partial-output
mode when available, and inspect the resulting row count before replacing a
corpus-wide record. `batches/README.md` documents known failures of this kind.

## Toolchain

The reproducibility target is Dafny 4.11.0 with Z3 5.1.0; `proofs.py` records
the Z3 it ran. Python needs `numpy` (`requirements.txt`): every row's `Input`
dataclass imports it, and without it every stored test fails to parse. It lives
in `bigodafny/.venv` (`uv venv && uv pip install -r requirements.txt`); run the
scripts with `.venv/bin/python`, not the system `python3`. Keep the version fixed for corpus-wide checks unless the task is
explicitly a toolchain upgrade.
