# Arms: the full approach against a baseline and two ablations

## Purpose

Measure how often each of four agent setups proves a tight bound on a row, on the same 60 rows.
`annotate` charges every row before any agent sees it. No agent sees a label.

| Arm | Before proving | Proving | Brief |
|---|---|---|---|
| `full` | names a class (`guess`) after running `fuzz.py` (1-3 calls) | `dafny verify`, 3 attempts | `full/PROMPT.md` |
| `nofuzz` | names a class from the code alone | same | `nofuzz/PROMPT.md` |
| `noguess` | nothing | same | `noguess/PROMPT.md` |
| `base` | nothing | same, may stop after one attempt | `base/PROMPT.md`: the output contract only |

- A brief is the `BRIEF.md` staged beside each row: the agent's whole task.
- Every arm writes `class`, the class it stands by, to `result.json`.
- `full`, `nofuzz` and `noguess` must use all 3 attempts unless they claim the bound is in `class`.
- Every arm has a 30-minute clock.
- Every bound must pass the prove campaign's audit (`stage.audit`); every `class` and `guess` must
  match `fuzz/guard.py`'s `CLASS`.

## Files

| File | Role |
|---|---|
| `manifest.jsonl` | the rows: `sid`, `stratum`, `path`, `truth`, `source`, `batch` |
| `setup.py` | stages one batch for one arm in `~/.cache/bigodafny-arms/<arm>/<sid>/` |
| `collect.py` | audits the staged batch, copies it to `runs/<arm>/<batch>/`, clears the stage |
| `report.py` | prints the tables over every collected batch |
| `judge.py`, `JUDGE.md` | the blind judge's input and output, and its brief |
| `<arm>/PROMPT.md` | the arm's brief |
| `<arm>/guard.py` | the hook of agent type `arms-<arm>` (`.claude/agents/arms-<arm>.md`): the arm's flags |
| `hook.py` | the rules behind every `guard.py`, on top of `prove_guard.py` run unchanged |
| `runs/` | git-ignored: each arm's batches, and `judged.jsonl` |

## Rows

- Pool: `solutions/` (`truth` is the label) and `solutions-disputed/` rows with cause `label`,
  confidence high and `true_class` not `other` (`truth` is the audited class in `data/label_audit.jsonl`).
- Strata by `truth`: `easy` (`O(1)`, `O(n)`) 10, `nlogn` 18, `n2` 16, `rare` (every other class) 16.
  A random draw would be half `O(n)`, which every proof campaign proved.
- The draw: the pool sorted by directory and SID, shuffled with seed 20261111, then taken in order,
  at most one row per problem, skipping `1387_34`, `1336_157` (need `counter=NAME`), `1972_295`
  (a row bug, `batches/prove-hard/README.md`) and rows `annotate` rejects (none).
- The first row of each stratum went to a trial of the harness, then out of the manifest; the next
  ones fill batches 1-4 of 15, each stratum spread evenly.

## Run

Run one batch per fresh Claude Code session, started in the repository root with the prompt
"Run batch K of `bigodafny/fuzzing/experiments/arms`, following its README § Run exactly." The session
works from this directory, with `../../../.venv/bin/python3` as Python, and changes no file here.

1. Check that `~/.cache/bigodafny-arms/` holds no arm directory and `runs/` holds no batch K.
2. For each arm, in the order `full`, `nofuzz`, `noguess`, `base`, finishing one before the next:
   1. `setup.py --arm A --batch K`.
   2. Spawn one `arms-A` agent per row, at most 3 at a time, starting the next when one finishes. The
      prompt is exactly "Your row is in DIR. Read DIR/BRIEF.md and do what it says.", DIR being the
      row's stage directory. Tell it nothing else, and never answer its messages.
   3. When every agent has finished, `collect.py --arm A --batch K`.
3. `judge.py export --batch K`. Spawn one `general-purpose` agent with `model: opus` and the prompt
   "Read bigodafny/fuzzing/experiments/arms/JUDGE.md, with {{BATCH}} = K and {{DIR}} =
   <this directory>/runs/judge/K, and do what it says." Then `judge.py import --batch K`.
4. `report.py`, and report to the user: its tables, each row's `audit_failures` and `stop_error`, and
   the guard denials per arm (`runs/<arm>/K/guard.log`).

If an agent ends on an API or harness error, or a script fails, stop and ask the user. Rerun nothing
on your own, and never rerun a row because its answer looks wrong.

`judged.jsonl` marks a proof tight when the judge finds its bound `equal` to `truth` or `tighter`.
