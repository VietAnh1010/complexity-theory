# `solutions/`: rows that passed every check

Each row here passes its tests and `dafny verify`, and the label audit found
no problem with its label. That does not prove the label; `solutions-proved/` does
that. `README.md` lists where the other rows are and why.

- A few rows use `decreases *` (`STATUS.md`): nothing proves they stop on
  every input.
- Layout: `solutions/<problem_id>/<solution_id>.dfy`. The header keeps the
  original Python and the generated signature.
