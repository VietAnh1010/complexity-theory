# Status

Every count about the corpus, in one file (`CLAUDE.md` § Counts).

Last checked against `data/` and the tree: 2026-10-13.

To refresh: re-run the scripts that write each source (`README.md` § Toolchain),
then read the numbers off the sources named in each section. Campaign
statistics are generated: `data/prove_stats.md` (`prove_stats.py`).

## Corpus

Source: `data/stats.json`, `data/dataset.jsonl`.

| Item | Count |
|---|---:|
| Rows | 640 |
| Problems | 311, all with a mapped `Solve` signature |
| Translated rows | 636 (the 4 in `solutions-untranslated/` are not) |
| Original Python reproduces its stored output exactly | 540 |
| Strict rows tested by `validate.py` | 534 |
| Strict rows that cannot be tested (`unvalidatable`) | 6: `1196_100`, `1196_51`, `1578_481`, `1578_724`, `1950_45`, `1950_47` |
| Loose rows | 100 |

## Directories

Source: the tree.

| Directory | Rows |
|---|---:|
| `solutions/` | 291 |
| `solutions-unscreened/` | 127 |
| `solutions-disputed/` | 202 |
| `solutions-unsure/` | 8 |
| `solutions-ungateable/` | 5 |
| `solutions-unverified/` | 3 |
| `solutions-untranslated/` | 4 |
| `solutions-proved/` (copies) | 321, of which 22 in `value-bounded/` |

## Gates

| Gate | Source | Result |
|---|---|---|
| `validate.py` | `data/validation.jsonl` | 534 rows: 533 `valid`, 1 `fail` (`1738_180`) |
| `difftest.py --loose` | `data/difftest.jsonl` | 100 rows: 95 `agrees`, 1 `differs` (`1501_224`, timeouts only), 4 `untranslated` |
| `verify_all.py` | `data/verification.jsonl` | 304 rows (`solutions/`, `solutions-unsure/`, `solutions-ungateable/`): all verify; 297 without `decreases *` |
| `proofs.py` | `data/complexity_proofs.jsonl` | 321 proofs: all verify, 0 `assume` |

Rows in `solutions/` using `decreases *`: 6.

## Label audit

Source: `data/label_audit.jsonl`.

| Verdict | Rows | Where they are |
|---|---:|---|
| `ok` | 296 | `solutions/` 291, `solutions-ungateable/` 4, `solutions-disputed/` 1 |
| `mismatch` | 201 | `solutions-disputed/` |
| `unsure` | 9 | `solutions-unsure/` 8, `solutions-ungateable/` 1 |

`solutions-disputed/` (202 rows):

| Item | Count |
|---|---|
| Round, by `auditor` field (an override counts in the round it overrides) | r3: 120, r4: 82 |
| Cause | `label` 159, `translation` 34, `both` 5, `harness` 3, none 1 (`1950_45`) |
| Confidence | high 101, medium 96, low 5 |
| `true_class: other` | 74 |
| With a proof in `solutions-proved/` | 52 |

`solutions-unsure/`: 6 of the 8 wait on the `ParseInt` charge.

`solutions-unscreened/` (source `data/quarantine.jsonl`): all 127 quarantined;
`sibling-convergence` 109, `set-build-quadratic` 22 (4 rows have both).

## Proofs

Source: `data/complexity_proofs.jsonl`, the tree.

| Row is in | Proofs |
|---|---:|
| `solutions/` | 264 |
| `solutions-disputed/` | 52 |
| `solutions-unsure/` | 4 |
| `solutions-unscreened/` | 1 |

Labels proved: `O(n)` 150 · `O(nlogn)` 67 · `O(n**2)` 40 · `O(1)` 32 ·
`O(n+m)` 14 · `O(n*m)` 11 · `O(nlogn+mlogm)` 4 · `O(logn)` 1 ·
`O(n+m)log(n+m)` 1 · `O(n**2+m**2)` 1.

## Proof campaigns

Source: `data/prove_stats.md`.

- 281 of 366 draws proved (77%), over 8 campaigns.
- 290 of the 329 distinct rows drawn carry a proof today (88%).
