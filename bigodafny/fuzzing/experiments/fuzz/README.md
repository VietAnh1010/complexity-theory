# Blind guess-only runs

## Purpose

A `blind-guess` agent names the tightest complexity class of one row's `Solve` without seeing
the row's label. The `code` mode reads the code only; the `fuzz` mode can also run `fuzz.py`.
`FINDINGS.md` holds the results so far.

## Files

| File          | Role                                                                                    |
| ------------- | --------------------------------------------------------------------------------------- |
| `blind.py`    | `setup` sets up rows for the agents; `grade` collects their answers and adds the labels |
| `BRIEF.md`    | the agent's task; `setup` keeps only the blocks marked for the row's mode               |
| `guard.py`    | the agent's hook: confines it to its row directory, lets Bash run only `fuzz.py`, blocks its stop until `answer.json` is complete, and logs each denial to `guard.log` |
| `guard-path`  | written by `setup`: the `--dir` that `guard.py` confines agents to (git-ignored)        |
| `fuzz.py`     | the agent's `fuzz` command: runs `gen.py`'s inputs on the row, prints one table of `steps` |
| `FINDINGS.md` | results of the runs of 2026-10-20                                                       |

## Run

From `bigodafny/fuzzing`. `--dir` must lie outside the repository:

1. Set up each mode:
   ```bash
   ../.venv/bin/python3 experiments/fuzz/blind.py setup --dir /tmp/fuzz-blind/guess2 --mode code 2072_40 888_6
   ../.venv/bin/python3 experiments/fuzz/blind.py setup --dir /tmp/fuzz-blind/guess2 --mode fuzz 2072_40 888_6
   ```
   Rows land in `/tmp/fuzz-blind/guess2/<mode>/<sid>/`.
2. For each row, spawn a `blind-guess` agent with the prompt "Your row is in
   DIR. Read DIR/BRIEF.md and do what it says.", DIR being the row directory. Run at most 3
   at a time, and tell the agent nothing else.
3. Grade:
   ```bash
   ../.venv/bin/python3 experiments/fuzz/blind.py grade --dir /tmp/fuzz-blind/guess2 --out experiments/fuzz/runs/guess2
   ```
   This copies the run to `--out`; `experiments/fuzz/runs/` is git-ignored.

## Outputs

Each row directory holds the files `setup` wrote and the agent's `answer.json`:

```json
{
  "class": "O(nlogn)",
  "measures": "n = |s|",
  "worst_case": "...",
  "example": "RYBG!!!!\n",
  "reasoning": "...",
  "confidence": "medium"
}
```

A `fuzz` row also holds `gen.py`, and any `round-k.dfy` the agent wrote to test a bound.

`runs/<run>/summary.jsonl` has one line per row: `sid`, `mode`, `label` (BigOBench's, added at
grading), the fields of `answer.json`, `match` (`class` equals `label` as a string), and `leaks`. `leaks` lists the guard's denials for the
row, and an `answer.json` still broken after 3 blocked stops; a nonempty list voids the row. Nothing checks what `gen.py` does: `BRIEF.md` only tells
the agent to make `gen.py` build input text and nothing else. `runs/<run>/README.md` is one
table: label, code mode, fuzz mode; `✓` marks a class equal to the label.
