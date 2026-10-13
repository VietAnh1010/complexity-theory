# `batches/`: one directory per campaign or migration

What each run was given and what came back, so a claim about a run can be
checked.

| Directory | Run | Contents |
|---|---|---|
| `labelaudit/` | the label audit | `PROMPT.md` and the verdict files |
| `cost-axioms/` | plan: fix collection costs by rule; drop `array<T>` | `PLAN.md` only |
| `gate-audit/` | seven rows that, when audited, sat in `solutions/` without a passing gate result | control results (`control.jsonl`) |
| `prove-sample/`, `prove-sample-2/` … `prove-sample-8/` | bounded proof campaigns | see `CAMPAIGN_CONFIG.md` |
| `value-bounded-open/` | value-bounded rows with no proof yet | `MANIFEST.jsonl` |
| `z3-upgrade/` | fixing proofs that time out under Z3 5.1.0 | instructions, trajectory, audit, attempts, transcripts |
| `output-length/` | re-charging proofs at one step per output character | instructions, trajectory, audit, attempts, transcripts |

## `labelaudit/`

- `PROMPT.md`: the auditor's instructions and cost model.
- `verdicts_<round>.jsonl`: one verdict per line, in the order applied; a later
  line for a row replaces an earlier one. `auditor` names the batch or marks
  an override. `data/label_audit.jsonl` holds the latest verdict per row.
- `verdicts_19.rejected.jsonl`: a batch `label_audit.py check` rejected.
- Evidence batches go to `out/labelaudit/` (git-ignored).

| Round | File | Date | Rules |
|---|---|---|---|
| r1 | `verdicts_r1-r2.jsonl` | 09-14 to 09-16 | costs taken from Dafny's Python output: a sequence or map update, or adding to a set, costs linear time |
| r2 | same file | 09-15 | r1's rules; the auditor also sees the problem statement. Redid batches 01–06, whose r1 verdicts survive only in git (`896e5fb`) |
| r3 | `verdicts_r3.jsonl` | 10-01 | input values are sizes; `IntToString` costs 1; `Gcd` costs Euclid's depth |
| r4 | `verdicts_r4.jsonl` | 10-01 | r3's rules plus the naming rule (`COMPLEXITY.md`) |

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
