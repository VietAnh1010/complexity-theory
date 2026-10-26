# Findings

Findings of the blind runs, newest first, one section per session.

## 2026-10-26: Haiku on the hard and fabricated rows

Batch `20261026-1540`: `blind-guess` with `model: haiku` (the Agent tool's override), both modes,
3 at a time. The 6 hard rows of `20261022-1327` and fabricated F3-F6 of `20261022-1353`, with
their `row.dfy` and statement. The fuzz brief now offers `--bound`; the Sonnet runs had `round-k.dfy`.

| row | reference | Sonnet code / fuzz | Haiku code | Haiku fuzz |
|---|---|---|---|---|
| 6 hard rows | audited class | 6 / 6 | 6 | 6 |
| F3, union by size | O(n+mlogn) | ✓ / ✓ | ✓ | ✓ |
| F4, union by size + compression | O(n+m) | ✓ / ✓ | O(n+mlogn), low | ✓ |
| F5, distinct counts | O(n**1.5) | ✓ / ✓ | O(n*m), m = distinct counts | ✓ |
| F6, phi chain | O(sqrt(m)) | ✓ / ✓ | ✓ | ✓ |

- Haiku code got 8 of 10; Haiku fuzz got 10 of 10. One agent per cell, so the 2-row gap may be noise.
- F4 code knew compression is near-linear, then answered the per-query bound with low confidence.
- F5 code derived `m <= sqrt(2n)` but kept `m`, a computed count, as the measure.
- F5 fuzz read the table: steps/n rose about 1.85x per 4x of n, so it answered `n**1.5`.
- F4 fuzz cited the amortized argument; its flat steps/(n+m) table agrees but did not decide it.
- 10 of 10 Haiku fuzz agents ran `--bound`, against 2 of 27 Sonnet fuzz agents before.
- F6 fuzz saw steps/E fall from 0.83 to 0.34 and blamed lower-order terms; the brief says looser.
- F3 fuzz said a bound cannot name a log; the prelude has `NLogN` and `CeilLog2`, used by `101_10`.
- `1830_0` fuzz is void: the guard denied `fuzz.py ... 2>&1 | tail -n 80`. The agent blamed its bound.
- The API was unreachable (`EAI_AGAIN`) mid-batch and killed 3 fuzz agents (`276_1206`, F3, F6).
  Their partial rows and 2 denials (`ls`/`cat`, a `cd ... &&` prefix) are in the run's `failed/`;
  the 3 rows were staged fresh and rerun.
- `blind.py grade` marks `match` against the host's label, so its table is wrong for F3-F6.

## 2026-10-22: fabricated rows with strange bounds

Batch `20261022-1353`: 4 fabricated rows, both modes, one-letter names, statements with input
format and limits only. Hosts `804_42 2128_34 2281_112 354_95`.

| row | trap | true class | code | fuzz |
|---|---|---|---|---|
| F3 | union by size, no compression; random inputs look linear | O(n+mlogn) | O(n+mlogn) | O(n+mlogn) |
| F4 | union by size with path compression | O(n+m), alpha | O(n+m) | O(n+m) |
| F5 | outer loop over distinct counts, inner loop over n | O(n**1.5) | O(n**1.5) | O(n**1.5) |
| F6 | k-deep recursion through phi, fast power, multiply | O(sqrt(m)) | O(m**0.5) | O(m**0.5) |

- All 8 answers are right; code mode needed no runs. Agents named union-find from structure
  alone, bounded distinct counts by sqrt(2n), and saw the phi chain end within 2 log m levels.
- Fuzz agents built the worst cases themselves: binomial-tree unions, a staircase of counts,
  prime m with k = 10**9. Each ran `fuzz` once.
- One bound test: F4's `round-1.dfy` with `ensures steps <= 40 * (n + m) + 20` gave a flat ratio
  of 0.66. Its diff in `table.txt` also lists the 30 header comment lines the agent dropped.
- `guard.log` holds 4 denials, which void F4, F5 and F6 fuzz: agents wrote `gen.py` with a Bash
  heredoc or ran `ls`, then used Write. None looked outside its row.
- F6's `A` (`while p * p <= n`) times out in `dafny verify`; `fuzz` compiles with `--no-verify`.

## 2026-10-22: fabricated rows

Batch `20261022-1342`: 2 fabricated rows, both modes. Each borrows a real row's stdin parser
(`2281_112`, `71_217`) and has its own `Solve` and statement; `blind.py grade` does not apply,
since it reads the host's label.

- F1, prefix sums at power-of-two positions: looks quadratic, is O(n). Both modes: O(n).
- F2, prefix sums at each new prefix maximum: random inputs give about n log n, increasing
  inputs n**2. Both modes: O(n**2).
- The F2 fuzz agent wrote an `increasing` family; the F1 fuzz agent sized n just above a power of
  two. Both ran `fuzz` once and tested no bound.
- Neither row misled a code-only agent: it read the geometric sum and the records worst case.

## 2026-10-22: hard rows, with `skipped` and `attempts/`

Batch `20261022-1327`, seed 20261022, both modes, 3 agents at a time. 3 rows from
`solutions-disputed/` (cause `label`, confidence high) whose audited class differs from the label:
`2610_1259 1830_0 276_1206`. 3 rows from `solutions/` with uncommon labels: `101_10 945_255
1243_178`.

- Code and fuzz mode gave the same class on all 6 rows.
- On the 3 disputed rows both modes gave the audited class, not the label: `2610_1259` O(n**2),
  `1830_0` O(n), `276_1206` O(n).
- `945_255` matched its label O(logn). `101_10` (O(nlogn), k <= n) and `1243_178` (O(n),
  |s1| = |s2|) stated the bound that the label's second measure collapses to.
- Every fuzz agent ran `fuzz` once on `row.dfy`, wrote one `gen.py` and tested no bound.
- Every `skipped` names the bound test and gives the table as the reason: "the doubling ratio
  (about 3.9-4.0x per doubling) over 5 sizes already shows a quadratic fit" (`2610_1259`).
- `276_1206`: 15 of 48 inputs timed out (family `big` at n = 20000), so the last table row shows
  family `small`. The agent answered from the other rows. Its row took 212 s; the others 23-45 s.
- Code rows took 9-18 s. `guard.log` stayed empty.
- `match` compares with the BigOBench label, so it marks the 3 audited-class answers wrong.

## 2026-10-22: `fuzz` as a script, live

Batch `20261022-1236`: 4 `20261021-1804` rows in fuzz mode, 3 agents at a time: `241_101 2282_16 2281_112 209_103`.

- Every agent ran Bash `fuzz.py` once, with `timeout: 600000`, and got a table.
- No `Connection closed`, although 2 agents ended while another's run was in flight.
- `guard.log` stayed empty: no denials, no blocked stops.
- No input failed `parse` or `out-of-spec`; `241_101` got step counts this time.
- All 4 matched the label; `2282_16` named its measure `n` this time. Rows took 25-37 s.
- No agent tested a candidate bound with `round-k.dfy`, in this batch or in `20261021-1804`
  (transcripts of all 14 fuzz agents: 1-2 `fuzz` calls each, all on `row.dfy`).
- Agents fix the class from the code, then run `fuzz` once to meet the brief's minimum:
  "Clearly O(n). Run fuzz once as required." (`2281_112`). `BRIEF.md` makes `round-k.dfy`
  optional, and the table on `row.dfy` already settles these rows.

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

### Batch `20261021-1804`

10 random rows from `solutions/`, one per problem, seed 20261021, none used before:
`2947_115 2282_16 307_14 1018_254 2281_112 241_101 209_103 493_134 499_359 187_762`.

- Code mode matched the label on 10 of 10; fuzz mode on 9. `2282_16` fuzz wrote `O(m**2)`, the
  right class with its measure named `m`.
- No guard denials and no blocked stops; code rows took 12-27 s, fuzz rows 39-105 s.
- `fuzz` returned `Connection closed` to 6 of 10 fuzz agents. Each came within 0.7 s of another
  `blind-guess` agent ending: the agents share one `fuzz` server, and an agent's end kills it.
- `241_101` got no step counts: its first `gen.py` gave inputs without a final newline, all
  `parse`, and its retry was killed. `2281_112` lost 6 inputs to `parse` the same way.

## 2026-10-20: blind runs

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
