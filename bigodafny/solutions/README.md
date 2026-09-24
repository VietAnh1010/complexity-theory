# `solutions/`: translated rows that passed their available checks

This directory contains 344 translated rows. Membership means the row is in the
screened corpus; it does not mean its complexity label has been proved.

A row normally arrives here after its behaviour gate passes, `dafny verify` has
no safety error, and the label screen has no recorded disagreement. The related
directories name work that is pending or disputed:

| directory | meaning |
|---|---|
| `solutions-unscreened/` | behaviour passed; label audit not run |
| `solutions-disputed/` | label, translation, or harness question remains |
| `solutions-ungateable/` | the harness cannot produce a normal verdict |
| `solutions-unverified/` | a safety or termination obligation remains |
| `solutions-untranslated/` | no faithful translation was made |
| `solutions-proved/` | overlay containing complexity proofs |

## Current checks

All 344 files pass `dafny verify`; ten still use `decreases *`, so they are not
termination proofs for every input. Complexity labels are proved only by the
304 files in `solutions-proved/`.

The cost model is the stipulated model in `COMPLEXITY.md`, not the implementation
cost of a particular Dafny backend. Sequence updates, map updates, and set
insertion are charged as constant-time operations; backend copying is recorded
as an implementation note rather than silently treated as a label mismatch.

## Layout

A file is `solutions/<problem_id>/<solution_id>.dfy`. Its header retains the
source Python and generated signature. Dataset, gate, and audit records remain
in `data/`; this README only explains the directory's meaning.
