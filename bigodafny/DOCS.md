# Working on BigODafny

BigODafny is self-contained under this directory. The repository root also has
an unrelated paper-mining project; do not mix its files or assumptions with
this corpus.

## Start here

Choose the path that matches the task.

| Task | Read |
|---|---|
| Understand the dataset | `README.md` |
| Change a translation or status | `CLAUDE.md`, then the affected `solutions*/README.md` |
| Review a label | `COMPLEXITY.md`, `solutions-disputed/README.md`, and `batches/labelaudit/PROMPT.md` |
| Write a complexity proof | `COMPLEXITY.md`, `solutions-proved/README.md`, and `batches/CAMPAIGN_CONFIG.md` |
| Understand campaign results | `data/prove_stats.md` |
| Read past work | `summaries/README.md` only after reading current documentation |

The summaries and old campaign prompts are historical records. They are useful
for provenance, but they are not operational instructions.

## Current state

| Item | Current value |
|---|---:|
| Rows / problems | 640 / 311 |
| Translated rows | 636 |
| Strict behaviour gate | 529 valid, 3 failed, 2 parser-blocked |
| Loose behaviour gate | 95 agree, 1 timeout-only unresolved, 4 untranslatable |
| Clean `solutions/` rows | 344 |
| Complexity proof files | 304, all verify without `assume` |
| Bounded campaign results | 281 proved of 366 draws (77%) |
| Distinct drawn rows with a proof now | 292 of 329 (89%) |
| Label-audited rows | 506: 347 ok, 152 mismatch, 7 unsure |

The status directories are the source of truth for a row's current state. Do
not infer state from an old campaign result or commit message.

## Status directories

| Directory | Meaning |
|---|---|
| `solutions/` | Behaviour-gated, safety-verified, and screened against its label. |
| `solutions-unscreened/` | Behaviour-gated but not yet audited for label accuracy. |
| `solutions-disputed/` | A review queue for label, translation, or harness questions. |
| `solutions-ungateable/` | The available evidence cannot support a normal behaviour verdict. |
| `solutions-unverified/` | A behaviour-gated translation with unproved safety obligations. |
| `solutions-untranslated/` | A row that cannot be represented faithfully enough to gate. |
| `solutions-proved/` | Instrumented proof copies; an overlay on the directories above. |

## The gates

A gate answers one narrowly defined question. Passing one does not imply that
the others passed.

| Tool | Question |
|---|---|
| `validate.py` | Does a strict row match BigO(Bench)'s stored output? |
| `difftest.py --loose` | Does a loose row match its original Python program? |
| `dafny verify` / `verify_all.py` | Are the stated safety and termination obligations discharged? |
| `precheck.py` | Do added preconditions accept the row's real inputs? |
| `proofs.py` | Does an instrumented complexity proof verify without `assume`? |
| `labelaudit.py` / `checkverdicts.py` | Is a label-audit record well formed and consistent with proofs? |

`solutions-ungateable/` exists for a different failure mode: the harness cannot
produce evidence that the gate needs. It does not mean the translation is known
to be wrong.

## Rules that protect the corpus

1. Trust tool output, not visual inspection.
2. Preserve the source algorithm, not just its output.
3. Do not change a gate while your work is being judged by it.
4. Treat subset commands that write shared JSONL as dangerous until verified.
5. Preserve failures and rejected work as records with an explanation.

## Complexity model

Collection costs are stipulated, not measured from the emitted Python. Sequence
update, map update, and set insertion are charged O(1); sequence concatenation
costs the length of its right operand; and a loop bounded by an input value is
parameterized by that value. See `COMPLEXITY.md` for the complete model.

Older records may use the backend-derived cost model. The records remain, but
they must not be reused as current guidance without checking their date.

## Campaign records

`batches/prove-sample*` preserves what bounded agents did: manifests define the
draw, `traj_*.jsonl` records attempts, `obstacles.jsonl` records unresolved
rows, and `label_relation.jsonl` records reviewed proof/label relationships.
Campaign 7 introduced `reads`, an ordered trace of material source, helper, and
prelude declarations consulted during a proof.

Campaign configurations and data formats changed over time. Read
`batches/CAMPAIGN_CONFIG.md` before pooling campaign numbers. `data/prove_stats.md`
is the normalized summary.
