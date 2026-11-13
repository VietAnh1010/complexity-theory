# `solutions-unsure/`: the label check could not decide

Rows that pass their tests and `dafny verify`, where the audit answered
`unsure`.
Each file's header gives the candidate class, evidence, and what to check.
Verdicts: `data/label_audit.jsonl` (from `batches/labelaudit/verdicts_r4.jsonl` and `verdicts_r5.jsonl`).

## Why

| row | label | candidate | open question |
|---|---|---|---|
| `1484_82` | O(nlogn) | O(nlogn) | is a phone number's fixed width a second size? |
| `2231_77` | O(n) | O(n) | `O(n)` only if the 26-letter alphabet is constant, which no `requires` says |
| `2680_65` | O(n**2+m**2) | other | the game runs until a deck state repeats; nothing bounds the rounds by a polynomial in n |

## Leaving

A reviewer decides:

- **Label right:** move the row to `solutions/` and drop the header.
- **Label wrong:** move it to `solutions-disputed/`, keep the header, and set
  the class.

Write the decision as a verdict file and run `label_audit.py apply` on it.
It moves the row, updates `data/label_audit.jsonl`, and archives the replaced
verdict in `data/old-record.jsonl`.
