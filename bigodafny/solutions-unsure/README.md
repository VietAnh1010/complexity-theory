# `solutions-unsure/`: the label check could not decide

Rows that pass their tests and `dafny verify`, where the audit answered
`unsure`.
Each file's header gives the candidate class, evidence, and what to check.
Verdicts: `data/label_audit.jsonl` (from `batches/labelaudit/verdicts_r4.jsonl`).

## Why

- **Most:** is an input number's digit count a size? The audit prompt charges
  `ParseInt` its text length; the proofs charge 1. Digits as a size gives
  `O(n*m)`; one machine word gives `O(n)`.
- `1484_82`: is a phone number's fixed width a second size?
- `2231_77`: `O(n)` only if the 26-letter alphabet is constant, which no
  `requires` says.

## Leaving

A reviewer decides:

- **Label right:** move the row to `solutions/` and drop the header.
- **Label wrong:** move it to `solutions-disputed/`, keep the header, and set
  the class.

Record the decision in `data/label_audit.jsonl`, moving the old line to
`data/old-record.jsonl`. `label_audit.py apply` makes the move.

| row | label | candidate | open question |
|---|---|---|---|
| `378_20` | O(n*m) | O(n*m) | numeral width |
| `378_91` | O(n) | O(n*m) | numeral width |
| `966_134` | O(n) | O(n*m) | numeral width |
| `976_1131` | O(n) | O(n) | numeral width |
| `1047_26` | O(n) | O(n*m) | numeral width |
| `2854_30` | O(n) | O(n*m) | numeral width |
| `1484_82` | O(nlogn) | O(nlogn) | fixed string width |
| `2231_77` | O(n) | O(n) | alphabet size |
