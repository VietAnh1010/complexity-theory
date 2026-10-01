# `solutions-unsure/` — the label audit could not decide

17 rows. Each passed its behaviour gate and `dafny verify`, like a row in
`solutions/`. The difference is the label: re-audit r3 (2026-10-01) returned
`unsure`, so the label is neither confirmed nor disputed.

Each file starts with the audit's header: the candidate class, the evidence,
and what a reviewer should check. The full verdict is in
`data/label_audit.jsonl`; the batch files are `batches/labelaudit/verdicts_r3*`.

## Why these were not decided

Most turn on what a label variable means, which BigOBench never states:

- whether string length is a size dimension (`O(n)` over n strings of length m);
- whether a second input list the label does not name is a second dimension;
- whether a statement cap on a count (not a loop bound) makes it constant.

## How a row leaves

A reviewer reads the header and decides:

- the label matches: move the file to `solutions/` and drop the header;
- it does not: move it to `solutions-disputed/`, keep the header, set the class.

Record the decision in `data/label_audit.jsonl` (the old line to
`data/old-record.jsonl`). `label_audit.py apply` does the move for a verdicts
file. Every gate still runs here: `validate.py`, `difftest.py`,
`verify_all.py` and `precheck.py` include this directory.

## Rows

| row | label | candidate | cause |
|---|---|---|---|
| `305_284` | O(n+m) | O(n+m) | translation |
| `378_20` | O(n*m) | O(n) | label |
| `380_112` | O(nlogn) | O(n+mlogm) | label |
| `577_509` | O(n) | O(n) | - |
| `662_527` | O(n) | O(n*m) | label |
| `662_559` | O(n**2) | O(n*m) | label |
| `1047_26` | O(n) | O(n) | - |
| `1177_230` | O(n) | O(n+m) | label |
| `1177_9` | O(nlogn) | O(nlogn+mlogm) | label |
| `1272_115` | O(n**2) | O(n**2) | label |
| `1272_278` | O(nlogn) | O(nlogn) | label |
| `1434_1616` | O(n**2) | O(n**2) | label |
| `1935_61` | O(n+m) | O(n) | - |
| `2193_70` | O(nlogn) | O(n**2) | translation |
| `2231_77` | O(n) | O(n**2) | translation |
| `2254_143` | O(n**2) | other | label |
| `2436_325` | O(n+m) | O(n) | harness |
