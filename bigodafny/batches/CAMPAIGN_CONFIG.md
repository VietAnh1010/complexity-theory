# Proof campaigns: reading the combined numbers

Eight campaigns ran from 2026-09-16 to 2026-09-24. Their settings differed, so
read these notes before combining their numbers.

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

## What changed between campaigns

- Every campaign charged a sequence update 1.
- From 2: an input value counts as a size.
- From 3: the relations `tighter-costmodel` and `tighter-translation` were added.
- From 6: `IntToString` costs 1. Campaigns 1–5 gave no rule for it.
- 7: only rows never drawn before (`--exclude-drawn`). Mid-run it started
  requiring `reads` traces (the declarations the agent read, in order), so 30
  rows were re-run on 2026-09-24. Its README separates the two settings.
- 8: drew all 18 rows never drawn before, so it is not a sample. Its
  instructions had the prelude's sort and binary-search lemmas from the start.

## Comparing

- Later draws kept re-drawing rows that had failed, so the raw rate fell from
  84% to 60% with the same budget. Compare fresh-row rates, or campaign 7 with
  campaign 1.
- `proofs.py` changed on 2026-09-22 and bounds were rewritten in a common form.
  Old records keep the agent's result; current files may hold a proof
  tightened later by hand. Don't mix them in one rate.
- A campaign's README gives what the agent achieved within budget;
  `old-record.jsonl` keeps replaced versions. `data/prove_stats.md` has the
  current totals.
