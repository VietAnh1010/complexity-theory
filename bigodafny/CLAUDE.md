# BigODafny rules

Read `DOCS.md` first. These rules apply to every edit of a translation, proof,
label verdict or status record.

## Keep the algorithm

The label belongs to the Python's algorithm, not just its output. Restructure
for Dafny only within the same complexity class. Don't swap a sort for a max,
a quadratic scan for a formula, or one sibling solution for another.

## Status directories

Each row is in exactly one of seven status directories (`README.md` lists
them). Move a row only when that directory's README allows it.
`solutions-proved/` is not one of them; it holds copies: add a proof by copying
the row there, and leave the original in place.

## Gates

- Strict rows: `validate.py`. Loose rows: `difftest.py --loose`.
- Passing tests shows behaviour, not safety or complexity.
- Run `precheck.py` whenever a fix adds a `requires`.
- No `var` binding inside a `requires`: state the clause over the parameters.
- Never weaken a gate to make the row under review pass.
- A test outside a limit the problem statement sets is bogus. Add the limit to
  `data/constraints.jsonl`, quoting the statement; the gates skip such tests
  and count them. Never infer a limit from where the code fails.

## Proofs

A proof may add ghost state, lemmas, `ensures`, invariants and `decreases`
clauses. It must not change what the program does.

- **A proof never changes the row's own `requires`.** If a proof needs a new
  precondition on the row's code:
  1. add it to the row, in the row's own directory;
  2. re-run the row's gates and `precheck.py` (every real input must pass);
  3. copy the changed row into the proof.

  Ghost helpers that only the proof adds may have their own `requires`.
- No `assume` in `solutions-proved/`, and no `decreases *` in a proof.
- An upper bound can confirm a label or show it too loose, never that the
  program is slower than the label; that needs a lower bound.

## Cost model

`COMPLEXITY.md` is the cost model. Never use measured timings instead.

## Record work honestly

- Record an unresolved row's real obstacle (missing invariant, nonlinear
  arithmetic, no termination measure, an unrelated value), not "ran out of
  time".
- Campaign trajectory records are append-only. Use the current schema (the
  `bigodafny-prove-campaign` skill and `vocab.py`), including `reads` (the
  declarations the agent read, in order) where required.
- Save every proof attempt to
  `batches/<campaign>/attempts/<problem_id>/<solution_id>.<n>.dfy`, failed
  ones included. Once the accepted proof is copied into `solutions-proved/`,
  delete only the attempt identical to it (ignoring the `include` line), and
  set that row's `final` field in `batches/<campaign>/audit.jsonl` to the
  proof's path.

## Docs describe the present

`DOCS.md`, `COMPLEXITY.md`, this file, the `solutions*/README.md` files and the
skills say what is true now: no "renamed from", "since <date>" or "an earlier
version said". When something changes, edit them in place and add one dated
bullet to `CHANGELOG.md`. Run records go in `batches/<campaign>/README.md`;
replaced data lines go in `old-record.jsonl`.

## Counts

Counts live only in `STATUS.md`. Don't write a count that changes when rows
move or proofs land (rows per directory, verdict counts, proof totals) into
any other doc; point to `STATUS.md`. When the corpus changes, update
`STATUS.md` from the data. Facts about one named row, fixed constants, and
history in `batches/` and `CHANGELOG.md` may keep their numbers.

`TODO.md` is a scratch list. Nothing in it flows into another doc.

## No one-off scripts

Delete a script written for one migration, campaign or repair before
committing; it won't work once the corpus changes. Describe what it did in the
batch README. Don't leave scratch inputs behind. Only tools the project runs
again belong in the tree.

Generated files nothing reads back go to `out/` (git-ignored, `common.OUT`).
`data/` holds only records a script or a person reads.

## Shared outputs

Before replacing a corpus-wide record, check its row count: a run on a subset
of rows can overwrite it (`batches/README.md` § The `--only` trap).

A script writing a `data/` record passes `key=` to `common.write_jsonl`, which
archives every replaced or dropped line in `old-record.jsonl`. Never move
record lines by hand.

## Toolchain

Keep the Dafny and Z3 versions in `README.md` fixed unless the task is an
upgrade (`proofs.py` records the Z3 it ran). Run scripts with the venv's
Python: without `numpy` every stored test fails to parse.
