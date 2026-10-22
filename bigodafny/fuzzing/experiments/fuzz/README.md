# Blind guess-only runs

## Purpose

A `blind-guess` agent names the tightest complexity class of one row's `Solve` without seeing
the row's label. In `code` mode it reads the code only; in `fuzz` mode it can also run
`fuzz.py`. `FINDINGS.md` holds the results.

## Files

| File                | Role                                                                                          |
| ------------------- | --------------------------------------------------------------------------------------------- |
| `blind.py`          | `setup` stages rows for the agents; `grade` collects their answers and adds the labels       |
| `BRIEF.md`          | the agent's task; `setup` keeps the blocks marked for the row's mode                         |
| `guard.py`          | the agent's hook: keeps it in its row, lets Bash run only `fuzz.py`, blocks its stop until `answer.json` is complete, logs denials to `guard.log` |
| `guard-path`        | temporary channel: `setup` writes the stage root, `guard.py` reads it (git-ignored)          |
| `fuzz.py`           | the agent's `fuzz` command: runs `gen.py`'s inputs on the row and prints one table of `steps` |
| `FINDINGS.md`       | results of the runs                                                                           |
| `FINDINGS.local.md` | where each run's outputs are on this machine (git-ignored)                                    |

## Run

Run from `bigodafny/fuzzing`. Name a batch by its setup time, `YYYYMMDD-HHMM`, and use that
name for both `--dir` (outside the repository) and `grade --out`.

1. Stage each mode:
   ```bash
   ../.venv/bin/python3 experiments/fuzz/blind.py setup --dir /tmp/fuzz-blind/20261022-1258 --mode code 2072_40 888_6
   ../.venv/bin/python3 experiments/fuzz/blind.py setup --dir /tmp/fuzz-blind/20261022-1258 --mode fuzz 2072_40 888_6
   ```
   Rows go to `/tmp/fuzz-blind/20261022-1258/<mode>/<sid>/`, beside one shared `prelude.dfy`.
2. For each row, spawn a `blind-guess` agent with the prompt "Your row is in DIR. Read
   DIR/BRIEF.md and do what it says.", DIR being the row directory. Run at most 3 at a time,
   and tell the agent nothing else.
3. Grade:
   ```bash
   ../.venv/bin/python3 experiments/fuzz/blind.py grade --dir /tmp/fuzz-blind/20261022-1258 --out experiments/fuzz/runs/20261022-1258
   ```
   `grade` copies the batch to `--out`; `experiments/fuzz/runs/` is git-ignored.

## Outputs

Each row directory holds the files `setup` wrote and the agent's `answer.json`. Only a
`fuzz` row has `skipped`:

```json
{
  "class": "O(nlogn)",
  "measures": "n = |s|",
  "worst_case": "...",
  "example": "RYBG!!!!\n",
  "reasoning": "...",
  "confidence": "medium",
  "skipped": "did not test a bound: the sort fixes O(nlogn)"
}
```

A `fuzz` row also holds `gen.py` and, for `fuzz` call k, `attempts/<k>/`:

- `table.txt`: the `.dfy` that ran, the bound E if `--bound` was given, the attempt whose
  `gen.py` ran, then the table;
- `gen.py`: only when `gen.py` changed since the last copy.

`runs/<batch>/summary.jsonl` has one line per row:

- `sid`, `mode`, and `label`, BigOBench's, added by `grade`;
- the fields of `answer.json`;
- `match`: `class` equals `label` as a string;
- `leaks`: the guard's denials for the row, and an `answer.json` still broken after 3 blocked
  stops. A nonempty list voids the row;
- in a `fuzz` row, `fuzz_calls`, `bound_tests` (calls with `--bound`) and `gen_versions`,
  counted from `attempts/`.

`runs/<batch>/README.md` is one table: label, code answer, fuzz answer, fuzz calls. `✓` marks
a class equal to the label.

Nothing checks what `gen.py` does: `BRIEF.md` only tells the agent to make it build input
text and nothing else.
