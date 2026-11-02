# `obstacle-review/`: what blocks the open rows

2026-11-02. The main agent read every attempt note for the drawn rows with no verified proof and
assigned the codes in `vocab.py`. Nothing was re-run. `traj.jsonl` has one dated line per coded row;
`why_failed` is copied from the line named by `source`.

- `1871_156` and `1972_295` take their note from `z3-upgrade`, where their proofs stopped verifying.
- `1364_161` and `2854_30` gave up in their latest draws. An earlier draw of each made a real attempt.

## Rows with no code

**No real attempt.** The latest notes show nothing was run, or only reasoning, and the agent stopped
under the 300-second budget. Any code would be a prediction, so retry them first:

`577_509`, `342_86`, `1306_126`, `514_90`, `2358_103`, `1582_315`, `1626_179`, `1332_16`, `1675_29`,
`2847_21`, `1263_2538`, `88_200`, `457_38`

**Translation gap.** The row omits a limit its problem statement gives, and the agent's note names that
as the blocker. Add the limit to the row, then re-run its gates and `precheck.py`:

| Row | The statement gives | The row has |
|---|---|---|
| `271_58` | `1 ≤ n` | no `requires` |
| `696_51` | `1 ≤ n` | `v_1 >= 1` only |
| `1861_16` | `H` between 1 and 100 | nothing on `a` |
| `2771_23` | `1 ≤ n` | `n >= 0` |
| `2819_926` | `1 ≤ k ≤ min(2⋅10^9, n(n-1)/2)` on each test | no limit on `k` |

`2282_437`, `281_12` and `2914_3` also omit a stated limit, but fixing it may not unblock them, so they
keep their codes.
