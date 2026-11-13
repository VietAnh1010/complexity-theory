# `batches/`: one directory per campaign or migration

What each run was given and what came back, so a claim about a run can be
checked.

| Directory | Run | Contents |
|---|---|---|
| `labelaudit/` | the label audit | `PROMPT.md` and the verdict files |
| `prove-sample/`, `prove-sample-2/` … `prove-sample-12/` | bounded proof campaigns | see § Combining campaign numbers |
| `prove-disputed-1/` … `prove-disputed-5/` | bounded campaigns on `solutions-disputed/` rows, proving the tightest bound | brief, slices, trajectories, relations, attempts, `README.md` |
| `value-bounded-open/` | value-bounded rows with no proof yet | `MANIFEST.jsonl` |
| `z3-upgrade/` | fixing proofs that time out under Z3 5.1.0 | instructions, trajectory, audit, attempts |
| `output-length/` | re-charging proofs at one step per output character | instructions, trajectory, audit, attempts |
| `prove-retry/` | a retry of the open rows, then every proof re-proved on `annotate`'s charges | brief, slices, trajectories, relations, attempts, `README.md` |
| `prove-hard/` | a blind rerun of the rows that had failed, to find hard rows | brief, trajectories, classification, attempts, `README.md` |

## Combining campaign numbers

The first eight campaigns ran from 2026-09-16 to 2026-09-24 with differing settings; read these
notes before combining their numbers. Later campaigns state their settings in their own README.

| campaign | date | draw |
|---|---|---:|
| `prove-sample` | 2026-09-16 | 50 |
| `prove-sample-2` | 2026-09-21 | 50 |
| `prove-sample-3` | 2026-09-21 | 50 |
| `prove-sample-4` | 2026-09-21 | 50 |
| `prove-sample-5` | 2026-09-22 | 48 counted |
| `prove-sample-6` | 2026-09-23 | 50 |
| `prove-sample-7` | 2026-09-23 | 50 |
| `prove-sample-8` | 2026-09-24 | 18 |

Campaign 5 counts 48 after removing two rows already proved; campaign 8 took
all 18 rows never drawn before.

### What changed between campaigns

- Every campaign charged a sequence update 1.
- From 2: an input value counts as a size.
- From 3: the relations `tighter-costmodel` and `tighter-translation` were added.
- From 6: `IntToString` costs 1. Campaigns 1–5 gave no rule for it.
- 7: only rows never drawn before (`--exclude-drawn`). Mid-run it started
  requiring `reads` traces (the declarations the agent read, in order), so 30
  rows were re-run on 2026-09-24. Its README separates the two settings.
- 8: drew all 18 rows never drawn before, so it is not a sample. Its
  instructions had the prelude's sort and binary-search lemmas from the start.

### Comparing

- Later draws kept re-drawing rows that had failed, so the raw rate fell from
  84% to 60% with the same budget. Compare fresh-row rates, or campaign 7 with
  campaign 1.
- `proofs.py` changed on 2026-09-22 and bounds were rewritten in a common form.
  Old records keep the agent's result; current files may hold a proof
  tightened later by hand. Don't mix them in one rate.
- A campaign's README gives what the agent achieved within budget;
  `old-record.jsonl` keeps replaced versions. `data/prove_stats.md` has the
  current totals.

## Reading a row's records

- **Older campaign lines were revised in place.** They carry `agent_outcome` and `agent_obstacle`,
  with replaced versions in `old-record.jsonl`. Campaign rates read `agent_outcome`.
- **`audit.jsonl` is a report.** It holds what `audit.py` found on its last run, so it can go stale, and
  `audit.py` overwrites it. Use `data/complexity_proofs.jsonl` for what verifies today.

## `labelaudit/`

- `PROMPT.md`: the auditor's instructions and cost model.
- `verdicts_<round>.jsonl`: one verdict per line, in the order applied; a later
  line for a row replaces an earlier one. `auditor` names the batch or marks
  an override. `data/label_audit.jsonl` holds the latest verdict per row.
- `verdicts_io-rule*.jsonl`: verdicts re-filed when parsing (`ParseInt`, `SplitWs`) began to cost `|s|` (`COMPLEXITY.md`).
- `verdicts_proved_<date>.jsonl`: verdicts set by a proof that corrects the label (`data/label_corrections.jsonl`).
- Evidence batches go to `out/labelaudit/` (git-ignored).

| Round | File | Date | Rules |
|---|---|---|---|
| r1 | `verdicts_r1-r2.jsonl` | 09-14 to 09-16 | costs taken from Dafny's Python output: a sequence or map update, or adding to a set, costs linear time |
| r2 | same file | 09-15 | r1's rules; the auditor also sees the problem statement. Redid batches 01–06; their r1 verdicts are not kept |
| r3 | `verdicts_r3.jsonl` | 10-01 | input values are sizes; `IntToString` costs 1; `Gcd` costs Euclid's depth |
| r4 | `verdicts_r4.jsonl` | 10-01 | r3's rules plus the naming rule (`COMPLEXITY.md`) |
| r5 | `verdicts_r5.jsonl` | 11-12 | r4's rules plus `ISqrt` costs `ISqrtSteps`; the unscreened rows and 38 disputed rows whose code was re-translated to follow the Python |

## The `--only` trap

A tool run on a subset of rows can replace a shared file with just that
subset. Four did:

| Tool | What it overwrote | Fix |
|---|---|---|
| `label_audit.py evidence --only` | a numbered `batch_NN.json` | writes `reaudit_NN.json` unless `--prefix` says otherwise |
| `difftest.py --only` | `data/difftest.jsonl` — it held 5 rows for a tier of 100 | merges by `solution_id` |
| `validate.py --only` | `data/validation.jsonl`, replacing its 532 rows | any `--only` or `--solutions-dir` run writes `out/<prefix>validation.jsonl` (default `partial_`) |
| `precheck.py SID...` | `data/precondition_check.jsonl` — it held one row's clauses | merges, replacing only the rows re-checked |

Assume any new subset tool has this bug until checked.
