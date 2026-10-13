# `solutions-unscreened/`: not yet label-audited

Rows that pass their tests but were left out of the label audit. Their
labels are neither known wrong nor known right.

## Why they were set aside

They were quarantined before the label audit existed, on two screens:

- **Sibling convergence** (`data/quarantine.jsonl`). `label_audit.py
  siblings` finds such pairs.
- **Using sets or maps**, because Dafny's Python output copies them on write.
  That screen no longer applies: `COMPLEXITY.md` charges them 1.

Many rows have no recorded reason at all (`STATUS.md`).

## Emptying it

```bash
python3 label_audit.py evidence --dir solutions-unscreened --prefix unscreened
```

Audit the batches with `batches/labelaudit/PROMPT.md`; each row then moves to
`solutions/` or `solutions-disputed/`. `label_audit.py apply` can't move rows
out of this directory yet: it only looks in `solutions/`,
`solutions-disputed/` and `solutions-unsure/`.
