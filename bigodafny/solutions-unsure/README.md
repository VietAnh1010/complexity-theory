# `solutions-unsure/` — the label audit could not decide

8 rows. Each passed its behaviour gate and `dafny verify`, like a row in
`solutions/`. The difference is the label: the audit returned `unsure`, so the
label is neither confirmed nor disputed.

Each file starts with the audit's header: the candidate class, the evidence,
and what a reviewer should check. The full verdict is in
`data/label_audit.jsonl`; the batch files are `batches/labelaudit/verdicts_r4*`.

## Why these were not decided

- **Six wait on one cost-model question:** is a numeral token's width a size?
  The brief charges `ParseInt` its argument's length; the proofs charge it 1,
  as `IntToString` is. Width as a size makes each `O(n*m)`; a machine-word
  token makes each `O(n)`.
- `1484_82`: the prefix loop walks a phone number's width, which the
  statement fixes; whether that width is a second size.
- `2231_77`: the code rebuilds a list of distinct letters per letter change;
  `O(n)` only if the 26-letter alphabet is constant, which no `requires` says.

## How a row leaves

A reviewer reads the header and decides:

- the label matches: move the file to `solutions/` and drop the header;
- it does not: move it to `solutions-disputed/`, keep the header, set the class.

Record the decision in `data/label_audit.jsonl` (the old line to
`data/old-record.jsonl`). `label_audit.py apply` does the move for a verdicts
file. Every gate still runs here: `validate.py`, `difftest.py`,
`verify_all.py` and `precheck.py` include this directory.

## Rows

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
