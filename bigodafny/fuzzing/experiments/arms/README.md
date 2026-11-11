# Arms: four agent setups on the same rows

## Purpose

Measure how often each of four agent setups proves a tight complexity bound, on the same 60 rows.
Before any agent starts, `annotate` adds the step charges to each row. No agent sees a row's label.

| Arm | Before proving | Brief |
|---|---|---|
| `full` | runs `fuzz.py` 1 to 3 times, then writes a guessed class | `full/PROMPT.md` |
| `nofuzz` | reads the code, then writes a guessed class | `nofuzz/PROMPT.md` |
| `noguess` | nothing | `noguess/PROMPT.md` |
| `base` | nothing; its brief gives only the output format | `base/PROMPT.md` |

Rules for every arm:

- The agent's whole task is its brief, copied into each row's folder as `BRIEF.md`.
- The agent gets 3 `dafny verify` runs and 5 minutes. Each `fuzz` call stops after 60 seconds.
- `full`, `nofuzz` and `noguess` must use all 3 runs, unless their bound is already in or below the
  class they state. `base` may stop after one run.
- The agent writes its final class to `result.json` as `class`, in the format `CLASS` in
  `fuzz/guard.py` accepts.
- A proof counts only if it passes the prove campaign's audit, `stage.audit`.
- The hook records whether each verify run passed. It keeps the agent from stopping while
  `result.json` names a failed run as `best_attempt`, or says `unresolved` although a run passed.
- In `full`, the hook denies writing `result.json` before the first `fuzz` call.

## Files

| File | Role |
|---|---|
| `manifest.jsonl` | the 60 rows and 4 trial rows: `sid`, `stratum`, `path`, `truth`, `source`, `batch` |
| `setup.py` | copies one batch for one arm into `~/.cache/bigodafny-arms/<arm>/<sid>/` |
| `collect.py` | audits that copy, moves it to `runs/<arm>/<batch>/`, and empties `~/.cache/bigodafny-arms/<arm>/` |
| `report.py` | prints the result tables over every collected batch |
| `JUDGE.md` | the brief of the agent that judges each bound against `truth` |
| `<arm>/PROMPT.md` | the arm's brief |
| `<arm>/guard.py` | the hook of agent type `arms-<arm>` (`.claude/agents/arms-<arm>.md`); it sets the arm's options |
| `hook.py` | the hook rules all arms share; it calls `prove_guard.py`, unchanged |
| `runs/` | results, git-ignored: one folder per arm and batch, and the judge's `judged-<batch>.jsonl` |
| `runs/pilot/` | the first run of batch 1, made before the hook recorded verify results; `report.py` ignores it |

## Rows

- Pool: rows in `solutions/`, where `truth` is the label, and rows in `solutions-disputed/` whose
  cause is `label`, with high confidence and a `true_class` other than `other`. For those, `truth`
  is the class in `data/label_audit.jsonl`.
- Strata by `truth`: `easy` (`O(1)`, `O(n)`) 10 rows, `nlogn` 18, `n2` 16, `rare` (every other
  class) 16. A random draw would be half `O(n)`.
- Draw: sort the pool by directory and SID, shuffle it with seed 20261111, and take rows in order,
  at most one per problem. `1387_34` and `1336_157` are skipped because they need `counter=NAME`,
  and `1972_295` because of a row bug (`batches/prove-hard/README.md`). `annotate` rejected no row.
- Batch `trial` holds the first row of each stratum and is for testing the harness. `report.py`
  ignores it, and `collect.py` overwrites its earlier run. The other rows form batches 1 to 4, 15
  rows each, spread evenly over the strata.

## Run

Run each batch in a fresh Claude Code session, started in the repository root with this prompt,
where K is the batch number:

> Run batch K of `bigodafny/fuzzing/experiments/arms`, following its README § Run exactly.

The session works in this directory, uses `../../../.venv/bin/python3` as Python, and changes no
file here.

1. Check that `~/.cache/bigodafny-arms/` has no arm folder and `runs/` has no batch K.
2. Do these steps for each arm, in the order `full`, `nofuzz`, `noguess`, `base`, finishing one arm
   before starting the next:
   1. Run `setup.py --arm <arm> --batch K`.
   2. Start one `arms-<arm>` agent per row, at most 3 at a time, and start the next row when an agent
      finishes. Give each agent exactly this prompt, with DIR replaced by the row's folder
      `~/.cache/bigodafny-arms/<arm>/<sid>`: "Your row is in DIR. Read DIR/BRIEF.md and do what it
      says." Tell it nothing else, and never answer its messages.
   3. When every agent has finished, run `collect.py --arm <arm> --batch K`. Each row's line ends
      with `hook recorded X of Y verify runs`. If X is less than Y, the hook missed a run: stop and
      ask the user.
3. Start one `general-purpose` agent with `model: opus` and this prompt: "Read
   bigodafny/fuzzing/experiments/arms/JUDGE.md, with {{BATCH}} = K, and do what it says."
4. Run `report.py`. Report to the user its tables, each row's `audit_failures` and `stop_error`, and
   each arm's hook denials, from `runs/<arm>/K/guard.log`.

If an agent ends on an API or harness error, or a script fails, stop and ask the user. Never rerun
anything on your own, and never rerun a row because its answer looks wrong.
