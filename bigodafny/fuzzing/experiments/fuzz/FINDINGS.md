# Findings

Findings of the blind runs, newest first, one section per session.

## 2026-10-21: pipeline review

No new runs; one test agent on `2072_40`. Changes are in `fuzzing/CHANGELOG.md`.

- Proofs made each blind row too expensive; the experiment now only guesses the class.
- `data/constraints.jsonl` quotes limits for few problems; for the rest `fuzz` runs any input.
- `gen.py` runs with full file access and can read the labels; `BRIEF.md` forbids it, nothing
  enforces it.
- An agent missing a tool falls back on another: without `fuzz` it tried Bash, then answered
  from the code alone.
- `guard.py` must allow the harness's own tools: denying `SubagentHandback` blocked the agent's
  report 4 times.
- `2072_40` again: `steps / n` goes 22.6, 19.8, 18.9, 19.1, 19.4 for n = 8 to 100. The fall
  is fixed overhead; the rise fits n log n but is too small to show it.
- The Stop hook works live: a `blind-guess` agent told to stop on `{}` was blocked once,
  read `BRIEF.md`, and wrote a complete answer (`888_6`, code mode).

### Batch `b10`

10 random rows from `solutions/`, one per problem, seed 20261021, none used before:
`2947_115 2282_16 307_14 1018_254 2281_112 241_101 209_103 493_134 499_359 187_762`.
Outputs: `experiments/fuzz/runs/b10/` (git-ignored, local).

- Code mode matched the label on 10 of 10; fuzz mode on 9. `2282_16` fuzz wrote `O(m**2)`, the
  right class with its measure named `m`.
- No guard denials and no blocked stops; code rows took 12-27 s, fuzz rows 38-105 s.
- `fuzz` returned `Connection closed` to 6 of 10 fuzz agents. Each came within 0.7 s of another
  `blind-guess` agent ending: the agents share one `fuzz` server, and an agent's end kills it.
- `241_101` got no step counts: its first `gen.py` gave inputs without a final newline, all
  `parse`, and its retry was killed. `2281_112` lost 6 inputs to `parse` the same way.

## 2026-10-20: blind runs

Outputs: `fuzzing/demo/blind/` (git-ignored, local).

### Loose proofs come from settling

Settling: proving a bound looser than the class the agent believes is tight, and
stopping because it verified.

Five proofs in `solutions-proved/` were a class too loose. Their agents saw the label.

| Row                 | Label     | Old proof | Tight     | Cause                                                                                |
| ------------------- | --------- | --------- | --------- | ------------------------------------------------------------------------------------ |
| `2586_20`           | O(n\*\*2) | O(n\*\*3) | O(n\*\*2) | inner scan bounded by the whole array, not the filled slots; recorded `looser-slack` |
| `1820_180`          | O(n)      | O(n\*\*2) | O(n)      | window bounded by list length, not x + y (statement: x, y <= 7)                      |
| `2913_484`          | O(n)      | O(n)      | O(sqrt n) | agent noted ~sqrt(x) iterations, proved 4n + 6 to match the label                    |
| `5_100`, `1011_368` | O(n)      | O(n)      | O(sqrt n) | no record                                                                            |

Why it happened:

- Success was "verifies"; nothing checked tightness.
- Tight bounds need amortization or nonlinear lemmas; Z3 timeouts exceed a 3-attempt budget.
- `looser-slack` ("a tighter proof was not attempted", `bigodafny/vocab.py`) was accepted.

Blind agents settle too:

- `bigodafny/experiments/proofs-blind/`: `1718_1166` predicted O(n*m), proved O((n+m)\*\*2);
  `1338_61` predicted O(n*m), proved O(q \* n\*\*2). Headers don't say if the tight bound was tried.
- This session (the prove brief asked for the tightest class first): no row settled on class.
  `1272_278` and `2913_484` settled on constants; `5_100` and `2586_20` ran out of budget.

Countermeasures:

- Write the predicted class before proving; a proof looser than it is a flaggable gap.
- Measure steps against the proved bound (`docs/07-steptrace.md`); this found all five.

### Runs do not improve guessing

- 12 hard rows, two blind Sonnet arms (code only; with `./fuzz`): both matched the
  reference class on all 12.
- Code only: 14-31 s a row. Runs added 30 s to 4 min and changed no answer.
- Small sizes mislead: `2072_40` (n <= 100) measured linear; the class is O(n log n).

### Where runs help

- Finding loose proofs.
- Catching a bound that is too low before proving (`1699_213` broke at n = 1).
- Evidence that a label is too low: steps outgrowing it. An upper-bound proof can't show this.
