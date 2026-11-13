# clean-636: every translated row clean, then `full` and `base` on all of them

Deadline: 2026-12-01. Started 2026-11-12.

## Goal

All 636 translated rows clean (the 4 rows in `solutions-untranslated/` stay out), then run the arms
`full` and `base` (`fuzzing/experiments/arms/`) on every row.

Decisions:

- A row's `truth` is a class backed by our own proof in `solutions-proved/`.
- A Dafny that does not follow its Python's algorithm is fixed, not relabelled.
- Code written in Dafny is never charged 1 step as a primitive: a prelude call costs its real steps
  (`Gcd` costs `GcdSteps`, `ISqrt` costs `ISqrtSteps`), the same in every row.

## A clean row

1. Its tests pass (`validate.py` strict, `difftest.py --loose` loose).
2. `dafny verify` passes, with no `decreases *` and no `assume`.
3. Every `requires` holds on every stored input (`precheck.py`).
4. It has a proof whose bound is in its `truth` class, and the proof compiles to the row's Python
   and keeps its `Solve` `requires` (`proofs.py`).
5. `annotate` accepts it.
6. Its `truth` is tight: measured steps grow like the proved bound.

`dataset.py` checks 1 to 4 per row as `blockers`; the counts are in `STATUS.md` § Clean rows.

## Pieces

Status is `done`, `open` or `partly`. Update this table with every commit that finishes a piece.

### A. Measure (12-14 Nov)

| # | Piece | Status |
|---|---|---|
| A1 | `dataset.py` writes `clean` and `blockers` per row | done `5b4d174` |
| A2 | `verify_all.py` sweeps every status directory | done `c3d5bee` |
| A3 | `proofs.py` checks every proof leaves its row unchanged | done `73e65cd` |
| A4 | `annotate` on all rows | done; its 2 rejections fixed in B5 |

### B. Every row valid and verified (14-19 Nov)

| # | Piece | Status |
|---|---|---|
| B1-B3 | rows failing `dafny verify` or using `decreases *` (`batches/verify-clean/`) | partly `943c08e`: 95 of 96; `1336_157` open |
| B4 | rows whose Dafny swaps the Python's algorithm (`batches/retranslate/`, `batches/isqrt/`) | done `f2fa883`, `a716343`, `b9654b2` |
| B5 | rename a row's own `steps` variable (`1387_34`, `1336_157`) | done `f35b2e7` |
| B6 | proofs that change their row: 40 `requires` copied to rows | partly `73e65cd`; `2496_30` open (`TODO.md`) |
| B7 | `1950_45`, `1950_47`: no test gate (`unvalidatable`, 100-digit reals) | open: all 42 tests parse, but the problem's own `Input.from_str` reads the number as a float, so the exact input never reaches Dafny; a harness fix |
| B8 | `1861_16`: a `requires` fails `precheck.py` | done: the failing test (`H = 0`) breaks the statement; `constraints.jsonl` has problem 1861 |

### C. A proved `truth` for every row (14-25 Nov)

| # | Piece | Status |
|---|---|---|
| C1 | `label_audit.py apply` finds rows in `solutions-unscreened/` | done (with C2) |
| C2 | label-audit the unscreened rows and the 38 disputed rows whose code changed in B4 (`batches/labelaudit/PROMPT.md`, updated for `ISqrt`) | done: `verdicts_r5.jsonl`, 167 rows: 71 ok, 95 mismatch, 1 unsure; 4 mismatch rows (`827_148`, `1944_50`, `2358_103`, `2819_926`) carry proofs of the label, settle in C4/C6 |
| C3 | `truth` lives in `data/label_corrections.jsonl`; a proof-backed correction moves a disputed row to `solutions/`; READMEs and `CHANGELOG.md` say so | open; proofs below an `ok` label: `1303_8` (`O(1)`, label `O(n**2)`), `1467_233` (`O(nlogn)`, label `O(n)`) |
| C4 | prove every row with no proof (`bigodafny-prove-campaign`), including proofs `proofs.py` flags as stale (`TODO.md`) | partly: `solutions/` done in `prove-sample-9`..`12` (79 of 80; `2282_1118` open); `solutions-disputed/` in `prove-disputed-1`..`4` (78 of 186; `1276_62` open, failed twice); stale proofs not started |
| C5 | prove C4's leftovers by hand | open: `2282_1118`, `1972_295` (no proof); `294_56`, `294_131` (add the statement's lowercase `requires`, then bound the distinct letters by 26) |
| C6 | write `truth` for disputed rows from their proofs | open; first, re-translate `1099_169`, `1054_212`, `101_43` (`batches/prove-disputed-1/README.md`) and `1437_223`, `799_94`, `949_67`, `1231_51`, `138_360` (`batches/prove-disputed-2/README.md`), `1054_216`, `619_340`, `1306_197`, `1593_264` (`batches/prove-disputed-3/README.md`), `1913_104`, `1413_222` (`batches/prove-disputed-4/README.md`): the Dafny does other work than the Python |
| C7 | settle the 2 unsure rows; re-audit `2381_156` | open |
| C8 | review `value-bounded/` proofs | open |

### D. `truth` is tight (25-27 Nov)

| # | Piece | Status |
|---|---|---|
| D1 | `steptrace.py` on every row's stored tests; flag rows where steps/bound shrinks with size | open |
| D2 | each flagged row: a tighter proof, or an input that reaches `truth` | open |
| D3 | freeze: `dataset.py` reports every row clean; full gate runs pass | open |

### E. Run `full` and `base` (27 Nov - 1 Dec)

| # | Piece | Status |
|---|---|---|
| E1 | `fuzzing/experiments/arms636/` with `full/`, `base/`, agent types `arms636-full`, `arms636-base`; scripts import `arms/` unchanged | open |
| E2 | `manifest.jsonl` of every row, `truth` from C | open |
| E3 | trial batch of 4 rows on both arms | open |
| E4 | all batches, `full` then `base` | open |
| E5 | report the tables | open |

## Resuming in a new session

1. Read this file, then `STATUS.md` § Clean rows and `TODO.md`.
2. Refresh the counts: `.venv/bin/python dataset.py`, then read `data/stats.json` (`clean`,
   `blockers`).
3. Continue with the first piece not `done`. The next C4 batch is `prove-disputed-5`:

   ```bash
   .venv/bin/python ../.claude/skills/bigodafny-prove-campaign/scripts/sample.py \
       --batch batches/prove-disputed-5 --dir solutions-disputed --n 20 --seed <YYYYMMDD> --slices 3
   ```

   Each slice's brief is `PROMPT.md` followed by `PROMPT_disputed.md` (the
   `bigodafny-prove-campaign` skill, step 2). After a batch, `.venv/bin/python proofs.py`
   re-verifies only changed proofs; run it when no agent is writing proofs.
4. Agent batches: ~20 rows per agent, 4 at a time, a `batches/<name>/` folder holding the brief
   (`PROMPT.md`), manifests and a `README.md` of results. Audit every batch from scratch before
   committing.
