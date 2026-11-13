# `prove-hard`

Rerun of the 64 rows that had failed in an earlier campaign, to find rows that an unhinted, budgeted
agent cannot prove. It is not a sample. Sonnet agents, one per row, 3 at a time.

**Result: no hard row, and 2 maybe-hard rows, `2423_48` and `1332_16`.** `classification.jsonl` has one
line per row.

| Group | Rows | Why |
|---|---|---|
| Difficult | none | no row failed every run |
| Maybe-difficult | `2423_48` | failed in 1 of 2 runs: showing the sorted list's last element came from the input |
| Maybe-difficult | `1332_16` | its proof timed out in 1 of 4 verify runs |
| Not counted | `1972_295` | row bug: its loops may not terminate for `k <= 0` |

A run is one fresh agent with 3 `dafny verify` attempts. 60 of the 64 rows have a proof from this batch
that passes the audit. The other 4 are `1332_16`, `1948_388`, `1944_50` and `1972_295`. No proof from this
batch is copied to `solutions-proved/`.

## Definitions

| Class | Meaning |
|---|---|
| `hard` | no audited proof, and the failure is a proof failure |
| `maybe-hard` | the proof is unstable, or the row failed in one run and passed in another |
| `not-hard` | an audited proof, or a failure caused by an oversight or the setup |
| `row-bug` | the row cannot be proved as stated |

## Method

- `stage.py setup` copies each row outside the repository: `annotate`'s output, a brief with the label,
  and a prelude with the comment lines naming a row removed.
- The `prove-blind` agent's hook, `prove_guard.py`, keeps the agent in its directory and denies any call
  if the hook itself fails.
- The hook allows 3 `dafny verify` runs on changed files and a 15-minute clock. It blocks an `unresolved`
  stop until the attempts or the clock run out.
- `stage.py collect` audits the last attempt: no banned construct, one `ensures steps <= E`, every
  `annotate` line kept in order, no changed `requires`, identical compiled Python, and 3 clean verify runs.
- An agent may replace an `invariant` line, because the verifier checks it. Moving any other line fails
  the audit.

## Results

| Measure | Rows |
|---|---:|
| Audited proofs | 59 |
| `hard` | 0 |
| `maybe-hard` | 2 |
| `not-hard`, audit failed | 2 |
| `row-bug` | 1 |
| Used 1 / 2 / 3 attempts | 39 / 20 / 5 |

Seconds per row: median 75, maximum 427. The hook logged 144 denials; none named a repository path.

| Row | Audit failure | Cause |
|---|---|---|
| `2423_48` | no proof after 3 attempts | could not show the sort's last element is in the input; the agent's last fix was never verified |
| `1332_16` | a verify run timed out | 3 later runs passed, so 1 of 4 runs failed |
| `1948_388` | banned `decreases *` | a leftover method-level clause; with that line removed by hand, 3 of 3 runs verified |
| `1944_50` | compiled Python differs | `annotate`'s output already differs from the row by a temporary variable; the proof's Python equals `annotate`'s |
| `1972_295` | no proof after 3 attempts | the row lacks a `requires`, so its loops may not terminate for `k <= 0` |

Of the 16 rows no bounded agent had proved, 15 have audited proofs here. Each row ran once, so a repeat
could differ.

## Relations

`label_relation.jsonl` has one line per proved row. The main agent read the Python of 21 rows: the 19 with
a relation other than `confirms`, and `88_200` and `1359_4`, whose bounds sit below their labels. It
compared the other 38 with their labels only. It changed 8 agent relations. The user has not reviewed them.

A loose bound does not make a row hard. The brief told agents to stop once an attempt verified, so a loose
bound does not show that a tighter one was out of reach.

## Rerun of loose bounds

`577_509`, `342_86`, `2819_926` and `1675_29` reran twice, to see whether a stricter brief gets tighter
bounds. The brief told agents to keep trying for a tighter bound and to name the attempt they stood by
(`best_attempt`). `traj_trial3.jsonl` is the first rerun. There agents left the hook's blocked stop through
the hand-back tool, so the hook now checks that tool too. `traj_trial4.jsonl` is the second rerun, where
agents also wrote `stop_reason`. All 4 used 3 attempts, and all 4 proofs pass the audit.
`label_relation.jsonl` still holds the bounds from the main run.

| Row | Bound in the main run | Bound in `traj_trial4.jsonl` | Result |
|---|---|---|---|
| `342_86` | sum of `v` | sum of `floor(sqrt(v))` | tighter class |
| `2819_926` | polynomial in each row's `n` and `k` | quadratic in each row's first value | simpler; the agent names `RepStr_steps`'s charge as the limit |
| `577_509` | linear in the sum of values | same, smaller constants | no change; the row lacks the statement's limit on values |
| `1675_29` | cubic | same | no change; the agent tried no different amortization |

`2423_48` also reran, after failing in the main run. `traj_trial5.jsonl` records a proof that passes the
audit: `2 * NLogN(|pairs|) + 11 * max(n,0) + 23 * (MaxFst(pairs) + 2) + 7 + |output|`. Its first attempt
failed, and its second and third verified. So the row failed in 1 of 2 runs.

## Files

| File | What it holds |
|---|---|
| `manifest.jsonl` | the 64 rows, their paths, labels and earlier outcomes |
| `PROMPT.md` | the brief template |
| `classification.jsonl` | each row's class, reason, relation and review flag |
| `label_relation.jsonl` | each proved row's bound, relation and reason |
| `traj_trial.jsonl` … `traj_trial5.jsonl`, `traj_main.jsonl` | records written by `stage.py collect` |
| `traj.jsonl` | dated lines after the audit began allowing replaced invariants |

## Run notes

- `1675_29` first stopped without a real attempt, twice. The hook and brief then changed, and its third
  run proved it. `traj_trial.jsonl` and `traj_trial2.jsonl` keep both records.
- `1386_19` first failed the audit by moving a line. It reran under the clearer brief and passed.
  `2831_71` and `2704_92` ran before the brief's wording on diligence and invariants changed.
- `2831_71` and `2704_92` lost their first trial to the 5-minute clock.
