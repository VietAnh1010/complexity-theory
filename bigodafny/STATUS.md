# Status

Every count about the corpus, in one file (`CLAUDE.md` § Counts).

Last checked against `data/` and the tree: 2026-11-13.

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
| Problems with stated limits in `data/constraints.jsonl`         | 9 (565, 577, 772, 827, 1254, 1276, 1501, 1861, 1954) |
| Stored tests skipped as outside those limits (public + private) |                                                        48 per 1501 row |

## Clean rows

Source: `data/stats.json` (`clean`, `blockers`), written by `dataset.py`. A row is clean when it
has no blocker. A row can carry several.

| Blocker | Meaning | Rows |
| --- | --- | ---: |
| `truth-unsettled` | label verdict is not `ok` (disputed, unsure, or never audited) | 258 |
| `unverified` | fails `verify_all.py` (`1336_157`) | 1 |
| `no-proof` | no proof in `solutions-proved/` | 102 |
| `decreases-star` | uses `decreases *` (`1336_157`) | 1 |
| `untranslatable` | in `solutions-untranslated/`; outside the target | 4 |
| `tests` | its gate has no pass; `1950_45`, `1950_47` (`unvalidatable`) | 2 |
| `precheck` | a `requires` clause fails `precheck.py` on the row | 0 |
| `proof-fails` | its proof does not verify or uses `assume` | 0 |
| `proof-changes-row` | its proof compiles to other Python or changes `Solve`'s `requires` (§ Known issues) | 11 |

Clean: 368 of 636 translated rows. `annotate` accepts every translated row.

## Directories

Source: the tree.

| Directory                    |                                 Rows |
| ---------------------------- | -----------------------------------: |
| `solutions/`                 |                                  374 |
| `solutions-unscreened/`      |                                    0 |
| `solutions-disputed/`        |                                  254 |
| `solutions-unsure/`          |                                    3 |
| `solutions-ungateable/`      |                                    4 |
| `solutions-unverified/`      |                                    1 |
| `solutions-untranslated/`    |                                    4 |
| `solutions-proved/` (copies) | 534, of which 42 in `value-bounded/` |

## Gates

| Gate                  | Source                         | Result                                                                                                       |
| --------------------- | ------------------------------ | ------------------------------------------------------------------------------------------------------------ |
| `validate.py`         | `data/validation.jsonl`        | 536 rows: all `valid`                                                                                        |
| `difftest.py --loose` | `data/difftest.jsonl`          | 98 loose rows: 94 `agrees`, 4 `untranslated`                                                                 |
| `verify_all.py`       | `data/verification.jsonl`      | 636 rows, every status directory: 635 verify; `1336_157` fails and uses `decreases *` |
| `proofs.py`           | `data/complexity_proofs.jsonl` | 534 proofs: all verify, 0 `assume`; 11 change their row (`2496_30`, and 10 written for code since changed)                                                                           |

Rows in `solutions/` using `decreases *`: 0.

## Label audit

Source: `data/label_audit.jsonl`.

| Verdict    | Rows | Where they are                                                       |
| ---------- | ---: | -------------------------------------------------------------------- |
| `ok`       |  378 | `solutions/` 374, `solutions-ungateable/` 3, `solutions-disputed/` 1 |
| `mismatch` |  253 | `solutions-disputed/`                                                |
| `unsure`   |    4 | `solutions-unsure/` 3, `solutions-ungateable/` 1                     |

`solutions-disputed/` (254 rows):

| Item                                                                     | Count                                                                    |
| ------------------------------------------------------------------------ | ------------------------------------------------------------------------ |
| Round, by `auditor` field (an override counts in the round it overrides) | r3: 85, r4: 72, r5: 95, io-rule: 2                                       |
| Cause                                                                    | `label` 215, `translation` 20, `both` 15, `harness` 3, none 1 (`1950_45`) |
| Confidence                                                               | high 125, medium 122, low 7                                              |
| `true_class: other`                                                      | 89                                                                       |
| With a proof in `solutions-proved/`                                      | 160                                                                      |

`solutions-unsure/`: 3 rows, each on its own question (`solutions-unsure/README.md`).

`solutions-unscreened/` is empty: label-audit r5 screened its rows. `data/quarantine.jsonl` keeps
the reasons they were quarantined: `sibling-convergence` 109, `set-build-quadratic` 22 (4 rows have both).

## Proofs

Source: `data/complexity_proofs.jsonl`, the tree.

| Row is in               | Proofs |
| ----------------------- | -----: |
| `solutions/`            |    372 |
| `solutions-disputed/`   |    160 |
| `solutions-unsure/`     |      2 |

Labels corrected by a proof (`data/label_corrections.jsonl`): 5. `O(n)` to `O(sqrt(n))` 3,
`O(nlogn)` to `O(n)` 1, `O(n*m)` to `O(n)` 1.

Proofs, by the row's BigOBench label: `O(n)` 227 · `O(nlogn)` 110 · `O(n**2)` 90 · `O(1)` 44 ·
`O(n*m)` 31 · `O(n+m)` 16 · `O(nlogn+mlogm)` 5 · `O(n+mlogm)` 5 · `O(logn)` 3 ·
`O(n**2+m**2)` 2 · `O(n+m)log(n+m)` 1.

## Proof campaigns

Source: `data/prove_stats.md`.

- 393 of 485 draws proved (81%), over 13 campaigns; `prove-retry` drew only open rows.
- `prove-disputed-1`..`5` proved 94 of 99 distinct disputed rows (open: `1276_62`, failed twice; `531_3456`, `2065_128`, `960_36`, `2854_107`); not label-proving draws, not counted.
- 407 of the 409 distinct rows drawn carry a proof today.
- The other 2 are open, coded by obstacle (`data/prove_stats.md` § Open rows now).

## Known issues

- `1336_157` fails `dafny verify`: `ProbeInsert` simulates CPython set probing and keeps
  `decreases *`.
- `1950_45`, `1950_47` have no test gate: the problem's `Input.from_str` reads the 100-digit
  coefficient as a float. Of the 23 tests that survive, they pass 7 and 19: both cut the fraction
  at 12 digits, where the Python uses `Decimal`.
- Proofs written for code since changed: `647_11`, `685_583` (re-translated to the Python's
  algorithm); `342_86`, `704_351`, `810_131`, `1944_50`, `1948_388`, `2358_103`, `2358_421`,
  `2819_926` (square roots now by `ISqrt`).
- `2496_30`'s proof adds loop caps (`padIter < 9`, `trimIter < 20`, `expIter < 2`) the row lacks;
  without them `FormatG9`'s trim loop is unbounded for values outside 10^-1000..10^1000.
- Dafny does other work than its Python (`solutions-disputed/`; each `prove-disputed-*/README.md`
  says how): `1099_169`, `1054_212`, `101_43`, `1437_223`, `799_94`, `949_67`, `1231_51`,
  `138_360`, `1054_216`, `619_340`, `1306_197`, `1593_264`, `1913_104`, `1413_222`, `333_197`,
  `397_163`.
- Label audit `ok`, proof disagrees: `1303_8`'s proof is tighter (`O(1)`, label `O(n**2)`);
  `1467_233`'s is looser (`O(nlogn)`, label `O(n)`), from the Python's `t += str(i)`.
- `2381_156`: its `O(1)` label and `ok` verdict (r3) predate the `IntToString` charge; its proof
  bounds `2 * Digits(n) + 4`.
- The audit's class is below the label, but the proof reaches only the label (`confirms`):
  `1180_626`, `2913_309`, `2913_484`.
- `2831_71` charges `IntToString` 1 step.
- `1972_295`: its proof times out under Z3 5.1.0 (`batches/z3-upgrade/unresolved/`).
- `810_131`, `1948_388` sit in `value-bounded/` though marked `looser-translation`; that directory
  takes only `looser-structural`.
- `dataset.py` gives the 6 `unvalidatable` rows `dafny_status: untranslated`, though they are
  translated.
- `audit.py` does not flag runs over budget: `2128_34`, `1582_118`, `2254_6`, `2704_92`, `2231_77`.
  `2254_6` and `2128_34` count as proved in campaign 1.
- `proofs.py` runs 8 `dafny verify` at once (`common.WORKERS`) and can run out of memory;
  `proofs.run(workers=2)` finishes.
