# `batches/` — work manifests, one directory per campaign

A manifest is a list of `solution_id`s handed to a batch of agents. They are
kept so a run is reproducible and so a claim about "wave 5" can be checked
against what wave 5 actually contained.

| directory | campaign | contents |
|---|---|---|
| `wave1/` … `wave7/` | translation | `.txt`, one sid per line |
| `loose/`, `loose2/` | translating the loose tier | `.txt` |
| `verify/`, `verify2/`, `verify3/` | discharging safety obligations | `.txt` |
| `labelaudit/` | the label audit | `PROMPT.md`, `verdicts_NN.jsonl`, and `batch_NN.json` (git-ignored) |
| `cost-axioms/` | `PLAN.md` — axiomatise collection cost; drop `array<T>` | plan only, no manifest |
| `stdlib-migration/` | `PROMPT.md` — move `prelude.dfy` call sites to `Std` | prompt only, not yet run |

## `labelaudit/` is the one that is not just manifests

- `PROMPT.md` — the agent prompt. Its prompt records the current stipulated cost model; a banner at
  the top says so, and `batches/cost-axioms/PLAN.md` step 2 replaces it.
- `verdicts_NN.jsonl` — the audit's output, one verdict per row. Committed:
  these are judgements, not a copy of the corpus.
- `verdicts_19.rejected.jsonl` — a batch the schema gate refused, kept as the
  record of a rejection.
- `batch_NN.json` — **git-ignored**. Each embeds a full `.dfy` and its Python,
  so they are 1.4M of content already committed elsewhere. Regenerate with
  `python3 labelaudit.py evidence`.

## The `--only` trap, four times

A tool that takes a subset of rows and writes a shared file will replace the
whole file with that subset unless someone stopped it. Four did:

| tool | what it clobbered | fix |
|---|---|---|
| `labelaudit.py evidence --only` | a numbered `batch_NN.json` | writes `reaudit_NN.json` unless `--prefix` says otherwise |
| `difftest.py --only` | `data/difftest.jsonl` — it held 5 rows for a tier of 100 | merges by `solution_id` |
| `validate.py --only/--limit` | `data/validation.jsonl` — 532 rows | writes `data/partial_validation.jsonl` unless `--out-prefix` is given |
| `precheck.py SID...` | `data/precondition_check.jsonl` — it held one row's clauses | merges, replacing only the rows re-checked |

`callgraph.py --only/--limit` was guarded the same way before it could bite.
If you add a tool that takes a subset and writes a shared file, assume it has
this bug until you have checked.
