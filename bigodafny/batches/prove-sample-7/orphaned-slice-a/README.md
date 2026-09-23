# Orphaned slice-A proofs

Slice A's agent was killed by a session rate limit part-way through its run.
It left **14 `.dfy` files under `solutions-proved/` with no trajectory record**
and had written only one trajectory line (`1039_15`, unresolved).

A proof with no trajectory is not campaign data: there is no attempt count, no
elapsed time, no label relation, and — under the reading-trace requirement
added to the brief — no `reads`. None of that can be recovered after the fact,
and none of it may be invented.

The files are held here, out of the overlay, so that **slice A could be re-run
as a real measurement**. Had they stayed in `solutions-proved/`, the re-run
agent would have opened a finished proof of its own assigned row and the
campaign would have measured nothing.

## Verification state when they were moved

Re-verified here, not taken on trust. 13 of 14 discharge cleanly; `2128_3`
times out, so that agent was still mid-proof when it was cut off.

| file | `dafny verify` |
|---|---|
| `1170_62` | 4 verified, 0 errors |
| `1511_65` | 1 verified, 0 errors |
| `1673_129` | 4 verified, 0 errors |
| `1739_170` | 1 verified, 0 errors |
| `2051_25` | 1 verified, 0 errors |
| `2128_3` | 7 verified, 0 errors, **1 time out** |
| `223_180` | 1 verified, 0 errors |
| `2482_151` | 1 verified, 0 errors |
| `2602_62` | 1 verified, 0 errors |
| `2773_120` | 1 verified, 0 errors |
| `3018_50` | 1 verified, 0 errors |
| `410_105` | 1 verified, 0 errors |
| `647_54` | 1 verified, 0 errors |
| `936_772` | 2 verified, 0 errors |

## What happens to them

Nothing automatic. They are **not** in `solutions-proved/`, so `proofs.py`
does not count them and no corpus number includes them. After the re-run, a
row the re-run also proved keeps the re-run's proof — the one with a
trajectory behind it. A row the re-run failed may have its file restored by
hand, but it is then a proof obtained **outside the budget** and must be
excluded from the campaign's rate, not folded into it.
