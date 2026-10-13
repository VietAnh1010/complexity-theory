# `batches/` — one directory per campaign or migration

Each holds what a run was given and what came back: the brief, the rows handed
out, the records the agents wrote, and the audit of them. They are kept so a
claim about a run can be checked against what it actually contained.

| directory | campaign | contents |
|---|---|---|
| `labelaudit/` | the label audit | `PROMPT.md`, one `verdicts_*.jsonl` per round, and `batch_NN.json` (git-ignored) |
| `cost-axioms/` | `PLAN.md` — axiomatise collection cost; drop `array<T>` | plan only, no manifest |
| `gate-audit/` | the seven `solutions/` rows with no passing gate result | control results (`control.jsonl`) |
| `prove-sample/`, `prove-sample-2/` … `prove-sample-8/` | bounded proof campaigns | see `CAMPAIGN_CONFIG.md` |
| `value-bounded-open/` | value-bounded rows with no proof yet | `MANIFEST.jsonl` |
| `z3-upgrade/` | repairing proofs that time out under Z3 5.1.0 | brief, trajectory, audit, attempts, transcripts |
| `output-length/` | re-charging proofs for one step per output character | brief, trajectory, audit, attempts, transcripts |

## `labelaudit/` is the one that is not just manifests

- `PROMPT.md` — the agent prompt. Its prompt records the current stipulated cost model; a banner at
  the top says so, and `batches/cost-axioms/PLAN.md` step 2 replaces it.
- `verdicts_<round>.jsonl` — the audit's output, one verdict per line, in the
  order applied; a later line for the same row supersedes an earlier one.
  `auditor` names the batch or the main-agent override. Committed: these are
  judgements, not a copy of the corpus.
- `verdicts_19.rejected.jsonl` — r1 batch 19 as first returned; the schema gate
  refused it. Kept as the record of a rejection.
- `batch_NN.json` — **git-ignored**. Each embeds a full `.dfy` and its Python,
  so they are 1.4M of content already committed elsewhere. Regenerate with
  `python3 label_audit.py evidence`.

The rounds. Each re-audit re-judges rows under the rules in force; `data/label_audit.jsonl`
holds the latest verdict per row.

| file | round | date | rules | rows | `auditor` |
|---|---|---|---|---:|---|
| `verdicts_r1-r2.jsonl` | r1 | 2026-09-14 to 09-16 | collection costs read off Dafny's Python backend: `s[i := v]`, `m[k := v]` and set insertion are linear | 340 | `labelaudit-batch-NN` (07–23) |
| | r2 | 2026-09-15 | r1's, with the problem statement given to the auditor; batches 01–06 redone, replacing r1's verdicts for them (those are in git at `896e5fb`) | 120 | `labelaudit-r2-NN` |
| `verdicts_r3.jsonl` | r3 | 2026-10-01 | input values are cost parameters; `IntToString` costs 1; `Gcd` costs Euclid's depth | 514 lines: `solutions/`, a fix-up batch, the `solutions-disputed/` queue, 1 override | `labelaudit-r3-NN`, `-r3-fix`, `-r3d-NN`, `main agent, …` |
| `verdicts_r4.jsonl` | r4 | 2026-10-01 | r3's rules plus the naming rule | 173 lines: disputed, solutions, unsure, 8 overrides | `labelaudit-r4-{d,s,u}NN`, `-r4-fix`, `main agent, …` |

## The `--only` trap, four times

A tool that takes a subset of rows and writes a shared file will replace the
whole file with that subset unless someone stopped it. Four did:

| tool | what it clobbered | fix |
|---|---|---|
| `label_audit.py evidence --only` | a numbered `batch_NN.json` | writes `reaudit_NN.json` unless `--prefix` says otherwise |
| `difftest.py --only` | `data/difftest.jsonl` — it held 5 rows for a tier of 100 | merges by `solution_id` |
| `validate.py --only` | `data/validation.jsonl` — 532 rows | any `--only` or `--solutions-dir` run writes `data/<prefix>validation.jsonl` (default `partial_`) |
| `precheck.py SID...` | `data/precondition_check.jsonl` — it held one row's clauses | merges, replacing only the rows re-checked |

`callgraph.py --only/--limit` was guarded the same way before it could bite.
If you add a tool that takes a subset and writes a shared file, assume it has
this bug until you have checked.
