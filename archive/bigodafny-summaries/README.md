# `summaries/` — the run log, in the order it happened

Sixteen write-ups, one per wave or sweep. They are a **record, not
documentation**: each says what was true when it was written, and several have
been overtaken since. Nothing here is merged or rewritten, because a summary
whose claims were later revised is the evidence that they were.

For what is true *now*, read `.claude/skills/bigodafny/SKILL.md`, the per-
directory `README.md` files, and `data/stats.json`. Read these for how the
corpus got there.

## Chronology

| date | file | what it covers |
|---|---|---|
| 08-31 | `wave3_batch1.md` … `wave3_batch4.md` | translation wave 3, one file per agent batch |
| 09-01 | `wave4.md` | wave 4, interrupted mid-run |
| 09-01 | `wave5.md`, `wave5_batches234.md` | wave 5; the second file covers batches 2–4 |
| 09-01 | `wave6.md` | wave 6 |
| 09-01 | `complexity_proofs.md` | the ghost-step-counter convention and the first proofs |
| 09-02 | `verification_pass.md` | `dafny verify` wave 1 of 3 |
| 09-02 | `verification_sweep.md` | `dafny verify` over all 452 translations; 32% clean |
| 09-02 | `wave7.md` | wave 7 — the last 80 strict rows |
| 09-07 | `loose_translation.md` | the loose tier and why `validate.py` is the wrong gate for it |
| 09-08 | `remaining_cases.md` | what was left after wave 7 |
| 09-08 | `verification_wave3.md` | `dafny verify` wave 3 |
| 09-09 | `proof_obstructions.md` | what blocks a complexity proof |

## Known superseded claims

| file | what changed |
|---|---|
| `proof_obstructions.md` | its 93-row "seq update" defect class is closed. `batches/cost-axioms/PLAN.md` charges `s[i := v]` O(1) by axiom, so those rows have no defect and need no repair. The file carries the correction inline. |
| `verification_sweep.md`, `wave7.md` | their directory names were updated in place to `solutions-unscreened/`; the **counts** beside them (106, 115) are that date's, not today's 127. |
| every wave file | row counts predate the label audit, which moved 178 rows into `solutions-disputed/`. |
