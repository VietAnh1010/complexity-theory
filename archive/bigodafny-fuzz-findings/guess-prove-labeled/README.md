# `guess-prove`

A pilot of 5 fabricated rows, run in two arms, to test whether an agent can prove a class it can name.
This directory holds the arm given the measured class. `../guess-prove-blind/` holds the arm that writes
its own guess first. Sonnet agents, one per row per arm, 3 at a time. Each row ran once.

## Results

"Audit" is `stage.py collect`. "Measured" is the true class in `fuzzing/experiments/fuzz/FINDINGS.md`.

| Row | Measured | Class given: bound | Audit | Guess | Own guess: bound | Audit |
|---|---|---|---|---|---|---|
| `F11` | `O(n**3)` | `60 n^3 + ...` | fail | `O(n^3)` | `60 n^3 + ...` | fail |
| `F12` | `O(n**3)` | `24 n^3 + ...` | pass | `O(n^2)` | `24 n^3 + ...` | pass |
| `F13` | `O(n**2)` | `33 n 5^n + ...` | pass | `O(n^2)` | `198 n^2 + ...` | pass |
| `F14` | `O(nlogn)` | none | fail | `O(n^2)` | `35 n^2 + ...` | pass |
| `F15` | `O(2**n)` | `290 n 2^n + ...` | pass | `O(n^2)` | none | fail |

| Measure | Class given | Own guess |
|---|---:|---:|
| Audited proofs | 3 | 3 |
| Audited proofs in the measured class | 1 | 2 |
| Also in the measured class, by the hand checks below | 1 | 1 |
| Guess equals the measured class | n/a | 2 |

## Failures and hand checks

| Row and arm | Audit failure | Hand check |
|---|---|---|
| `F11` given | `{:isolate_assertions}` on `Settle` changes an `annotate` line | 3 of 3 verify runs pass; without the attribute, `Settle` times out |
| `F11` guess | attempt 3 has an indentation warning, so `dafny verify` exits non-zero | with `--allow-warnings`, 3 of 3 pass; the final `proof.dfy` passes the audit |
| `F14` given | no attempt verified | the final `proof.dfy`, never run by the agent, passes the audit, with a quadratic bound |
| `F15` guess | keeps `decreases *`, and has no bound | none: the agent reports `termination-not-proved` |

The hand checks do not change `traj_main.jsonl`. An attempt the agent never ran is outside its budget.

## Notes

- `F13` given: the agent wrote that one walk on `[0,1,...,1]` takes `2^n - 1` iterations. A simulation
  gives 58 at `n = 20`. The worst single walk over every configuration up to `n = 14` is `3n - 2`.
- Budget: no agent reached the 15-minute clock. The longest took 463 s.
- Guesses: the first write to `result.json` came before the first edit of `proof.dfy` in all 5 runs of the
  own-guess arm, checked in the transcripts.
- Guess-only runs named `F12`–`F15` correctly once each. In this run, the same model missed `F12`, `F14` and `F15`.
- Every bound is an upper bound. "Measured" classes come from `fuzz.py` runs and the arguments in `FINDINGS.md`.

## Method

- `rows/` holds `f11.dfy`–`f15.dfy`, copied from `fuzzing/experiments/fuzz/runs/`, git-ignored there.
- `f11`, `f12`, `f13` and `f15` each gained one `requires` on the helper, stating the array's value range.
  Without it the helper accepts values that break any step bound, and the brief forbids an agent adding one.
  All 4 clauses hold at every call: `Solve`'s own `requires` give `F11`'s range, and the other 3 helpers
  keep their array's values in range. This was argued by hand, not run through `precheck.py`, because these
  rows have no stored tests. Compiled Python is identical on all 5 rows, before and after `annotate`.
- `PROMPT.md` in this directory is `prove-hard`'s brief unchanged. The other arm's differs only in its title
  and in replacing the label line with an order to write `guess` and `guess_basis` before editing `proof.dfy`.
- A row's id is `F11_L` here and `F11_B` in the other arm, because both share one stage directory.

## Files

| File | What it holds |
|---|---|
| `manifest.jsonl` | the rows, their paths and measured classes |
| `traj_main.jsonl` | records written by `stage.py collect` |
| `results/` | each agent's `result.json`, with `guess` in the other arm, and its `budget.json` |
| `attempts/` | every attempt the audit collected |
