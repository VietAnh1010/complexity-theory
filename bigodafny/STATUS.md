# Status

Every count about the corpus, in one file (`CLAUDE.md` § Counts).

Last checked against `data/` and the tree: 2026-11-03; § Clean rows, § Directories, § Gates: 2026-11-12.

To refresh: re-run the scripts that write each source (`README.md` § Toolchain),
then read the numbers off the sources named in each section. Campaign
statistics are generated: `data/prove_stats.md` (`prove_stats.py`).

## Corpus

Source: `data/stats.json`, `data/dataset.jsonl`.

| Item                                                            |                                                                  Count |
| --------------------------------------------------------------- | ---------------------------------------------------------------------: |
| Rows                                                            |                                                                    640 |
| Problems                                                        |                               311, all with a mapped `Solve` signature |
| Translated rows                                                 |                       636 (the 4 in `solutions-untranslated/` are not) |
| Original Python reproduces its stored output exactly            |                                                                    542 |
| Strict rows tested by `validate.py`                             |                                                                    536 |
| Strict rows that cannot be tested (`unvalidatable`)             | 6: `1196_100`, `1196_51`, `1578_481`, `1578_724`, `1950_45`, `1950_47` |
| Loose rows                                                      |                                                                     98 |
| Problems with stated limits in `data/constraints.jsonl`         |                                         6 (1501, 577, 827, 1254, 1276, 1954) |
| Stored tests skipped as outside those limits (public + private) |                                                        48 per 1501 row |

## Clean rows

Source: `data/stats.json` (`clean`, `blockers`), written by `dataset.py`. A row is clean when it
has no blocker. A row can carry several.

| Blocker | Meaning | Rows |
| --- | --- | ---: |
| `truth-unsettled` | label verdict is not `ok` (disputed, unsure, or never audited) | 329 |
| `unverified` | fails `verify_all.py` (`1336_157`) | 1 |
| `no-proof` | no proof in `solutions-proved/` | 275 |
| `decreases-star` | uses `decreases *` (`1336_157`) | 1 |
| `untranslatable` | in `solutions-untranslated/`; outside the target | 4 |
| `tests` | its gate has no pass; `1950_45`, `1950_47` (`unvalidatable`) | 2 |
| `precheck` | a `requires` clause fails `precheck.py` on the row (`1861_16`) | 1 |
| `proof-fails` | its proof does not verify or uses `assume` | 0 |
| `proof-changes-row` | its proof compiles to other Python or changes `Solve`'s `requires` (`2496_30`; 10 rows whose code changed, `TODO.md`) | 11 |

Clean: 289 of 636 translated rows. `annotate` accepts every translated row.

## Directories

Source: the tree.

| Directory                    |                                 Rows |
| ---------------------------- | -----------------------------------: |
| `solutions/`                 |                                  303 |
| `solutions-unscreened/`      |                                  129 |
| `solutions-disputed/`        |                                  197 |
| `solutions-unsure/`          |                                    2 |
| `solutions-ungateable/`      |                                    4 |
| `solutions-unverified/`      |                                    1 |
| `solutions-untranslated/`    |                                    4 |
| `solutions-proved/` (copies) | 361, of which 29 in `value-bounded/` |

## Gates

| Gate                  | Source                         | Result                                                                                                       |
| --------------------- | ------------------------------ | ------------------------------------------------------------------------------------------------------------ |
| `validate.py`         | `data/validation.jsonl`        | 536 rows: all `valid`                                                                                        |
| `difftest.py --loose` | `data/difftest.jsonl`          | 98 loose rows: 94 `agrees`, 4 `untranslated`                                                                 |
| `verify_all.py`       | `data/verification.jsonl`      | 636 rows, every status directory: 635 verify; `1336_157` fails and uses `decreases *` |
| `proofs.py`           | `data/complexity_proofs.jsonl` | 361 proofs: all verify, 0 `assume`; 11 change their row (`2496_30`, and 10 written for code since changed)                                                                           |

Rows in `solutions/` using `decreases *`: 0.

## Label audit

Source: `data/label_audit.jsonl`.

| Verdict    | Rows | Where they are                                                       |
| ---------- | ---: | -------------------------------------------------------------------- |
| `ok`       |  307 | `solutions/` 303, `solutions-ungateable/` 3, `solutions-disputed/` 1 |
| `mismatch` |  196 | `solutions-disputed/`                                                |
| `unsure`   |    3 | `solutions-unsure/` 2, `solutions-ungateable/` 1                     |

`solutions-disputed/` (197 rows):

| Item                                                                     | Count                                                                    |
| ------------------------------------------------------------------------ | ------------------------------------------------------------------------ |
| Round, by `auditor` field (an override counts in the round it overrides) | r3: 115, r4: 80, io-rule: 2                                              |
| Cause                                                                    | `label` 154, `translation` 34, `both` 5, `harness` 3, none 1 (`1950_45`) |
| Confidence                                                               | high 101, medium 91, low 5                                               |
| `true_class: other`                                                      | 71                                                                       |
| With a proof in `solutions-proved/`                                      | 68                                                                       |

`solutions-unsure/`: 2 rows, each on its own question (`solutions-unsure/README.md`).

`solutions-unscreened/` (source `data/quarantine.jsonl`): 127 of 129 quarantined (`1369_10`, `1369_14` came from `solutions-unverified/`);
`sibling-convergence` 109, `set-build-quadratic` 22 (4 rows have both).

## Proofs

Source: `data/complexity_proofs.jsonl`, the tree.

| Row is in               | Proofs |
| ----------------------- | -----: |
| `solutions/`            |    290 |
| `solutions-disputed/`   |     68 |
| `solutions-unsure/`     |      2 |
| `solutions-unscreened/` |      1 |

Labels corrected by a proof (`data/label_corrections.jsonl`): 5. `O(n)` to `O(sqrt(n))` 3,
`O(nlogn)` to `O(n)` 1, `O(n*m)` to `O(n)` 1.

Labels proved, by BigOBench's label: `O(n)` 165 · `O(nlogn)` 76 · `O(n**2)` 53 · `O(1)` 33 ·
`O(n+m)` 14 · `O(n*m)` 12 · `O(nlogn+mlogm)` 4 · `O(logn)` 2 ·
`O(n+m)log(n+m)` 1 · `O(n**2+m**2)` 1.

## Proof campaigns

Source: `data/prove_stats.md`.

- 314 of 405 draws proved (78%), over 9 campaigns; `prove-retry` drew only open rows.
- 328 of the 329 distinct rows drawn carry a proof today.
- The other 1 is open, coded by obstacle (`data/prove_stats.md` § Open rows now).
