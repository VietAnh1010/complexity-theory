# `solutions-unscreened/`: not yet label-audited

Rows that pass their tests but were left out of the label audit. Their
labels are neither known wrong nor known right.

## Why they were set aside

They were quarantined before the label audit existed. `data/quarantine.jsonl`
gives each row's reasons:

- `sibling-convergence`: the row converged with a sibling that has a different
  label. `label_audit.py siblings` finds such pairs.
- `set-build-quadratic`: the row builds a `set` in a loop, which Dafny's Python
  output copies on every insert. This reason no longer applies:
  `COMPLEXITY.md` charges set insertion 1.

## Emptying it

```bash
python3 label_audit.py evidence --dir solutions-unscreened --prefix unscreened
```

Audit the batches with `batches/labelaudit/PROMPT.md`; each row then moves to
`solutions/` or `solutions-disputed/`. `label_audit.py apply` can't move rows
out of this directory yet: it only looks in `solutions/`,
`solutions-disputed/` and `solutions-unsure/`.
