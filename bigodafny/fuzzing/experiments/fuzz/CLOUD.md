# Cloud run: blind guess-measure-prove on disputed rows

Instructions for an agent picking up this work in a cloud session. Read
`bigodafny/fuzzing/README.md` and `BRIEF.md` (beside this file) first.

## Purpose

Each row's `Solve` carries a ghost step counter. A `blind-fuzz` agent, which never sees the row's
complexity label, guesses a bound from the code, measures it with generated inputs, tightens
it, and proves it. You stage the rows, run the agents, grade them, and push the results.
You are not measured, so you may read the repository; the agents may not.

## 1. Check the environment

Run from the repository root. Stop at the first failure and write it to the results README
(step 5) instead of working around it.

| Check | Expect |
|---|---|
| `dotnet --list-sdks` | a `10.0.x` SDK (`DafnySteps` targets net10.0) |
| `dafny --version` | `4.11.0` |
| `z3 --version` | `5.1.0` |
| `ls ~/.dotnet/tools/.store/dafny/4.11.0/dafny/4.11.0/tools/net8.0/any/DafnyCore.dll` | exists (`fuzzing/Directory.Build.props` builds against it) |
| `bigodafny/.venv/bin/python3 -c "import numpy"` | no error |
| `ls bigodafny/data/tasks.jsonl` | exists (git-ignored, 79 MB) |
| `cd bigodafny/fuzzing && dotnet build -c Release DafnySteps && dotnet test DafnySteps.Tests` | build succeeds; all tests pass |
| `ls .claude/agents/blind-fuzz.md` | exists; the Agent tool lists `blind-fuzz` |

Fixes, if the environment's setup script does not already do them:

```bash
curl -sSL https://dot.net/v1/dotnet-install.sh | bash -s -- --channel 10.0   # .NET 10 SDK
dotnet tool install --global dafny --version 4.11.0
python3 -m venv bigodafny/.venv && bigodafny/.venv/bin/pip install numpy
cd bigodafny && .venv/bin/python3 extract.py      # downloads BigOBench from huggingface.co
```

If `blind-fuzz` is missing from the Agent tool's list, the session started before the file
existed; it cannot be added mid-session. Record that and stop.

## 2. Stage

Pick a run id, e.g. `cloud-YYYYMMDD`. Stage outside the repository:

```bash
cd bigodafny/fuzzing
ROOT=/tmp/fuzz-blind/<run-id>
../.venv/bin/python3 experiments/fuzz/stage.py $ROOT 2505_30 2282_437 1830_0 1263_2538 \
  1622_305 2830_421 1820_122 2607_25 1733_49 2650_140 554_70 1047_641 1263_1960 1626_179 \
  577_656 342_149 2723_42 1272_115 795_300
mkdir -p ../out && echo $ROOT > ../out/fuzz-confined
```

These 19 rows are in `solutions-disputed/`: a label audit judged their label wrong, so the
cost is not obvious. All 19 annotate cleanly and none has `decreases *`.
`stage.py` aborts if a staged file contains the label; do not edit a staged file to get past it.

## 3. Run the agents

For each row, spawn one agent with the Agent tool: `subagent_type: "blind-fuzz"`, prompt

> Your row is staged in ROOT/SID. Read ROOT/SID/BRIEF.md and do what it says.

Run at most 3 at a time, in the order above. Do not tell an agent anything else about its row.
The agent type's own hook (`guard.py`) confines it to ROOT. If the session budget runs low,
stop launching and grade what finished.

## 4. Grade

```bash
cd bigodafny/fuzzing
../.venv/bin/python3 experiments/fuzz/grade.py $ROOT experiments/fuzz/runs/<run-id>
```

`grade.py` re-verifies each claimed proof, rejects `assume` and `decreases *`, checks the proof
compiles to the same Python as the row, joins the label, and copies each row's directory.
A row with a nonzero `leaks` count is void: say so, do not drop it.

## 5. Write up and push

Add to `runs/<run-id>/README.md`, below the table `grade.py` wrote:

- the environment check (step 1), and anything you had to fix;
- per row, one line: the guess from code, the measured class, the proved class, and
  how each compares with the label (equal, tighter, looser);
- rows where the measured class differs from the guess from code: those are what this
  workflow is for;
- tool problems the agents reported in `record.json` `notes`.

Commit only `bigodafny/fuzzing/experiments/fuzz/runs/<run-id>/`. Do not change the tools, the
rows, or anything else; a tool bug goes in the README. Push to a branch of its own, named
`fuzz-runs/<run-id>` if you can choose the name. The results can then be read with
`git fetch origin <branch>` and dropped by deleting the branch.
