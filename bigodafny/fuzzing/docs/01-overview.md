# 1. Overview

## The tools

| Tool | Question it answers |
|---|---|
| `steptrace.py` | What is `steps` on each input? Does the proved bound hold? |
| `stepfuzz.py` | For each input size, which input makes `steps` largest? |
| `DafnySteps deghost` | Which program does `steptrace.py` compile? (06) |
| `DafnySteps annotate` | Where does a step counter go in a plain row, and what does each statement cost? (09) |

## Layout

```
fuzzing/
  steptrace.py          run one row's counter on inputs
  stepfuzz.py           search for costly inputs; uses steptrace.py
  scripts/demo.sh       deghost + annotate (+ steptrace) on one row -> demo/<problem>/
  DafnySteps/           C#: the deghost and annotate passes, as a CLI and a Dafny plugin
  DafnySteps.Tests/     golden tests for DafnySteps
  Directory.Build.props where the Dafny install is
  TODO-fuzzing.md       open items
```

## Data flow

```
solutions-proved/P/SID.dfy           proof copy: ghost steps, proved bound
   │  dafny translate py, with DafnySteps as a plugin: steps becomes compiled
   ▼
.build/trace_SID_t/out-py/           Python; Solve(..) returns (output, steps)
   │  steptrace.py runs it on each input
   ▼
out/trace/SID.jsonl                  steps per input
out/fuzz/SID.json                    stepfuzz.py: costliest input per size
```

`annotate` is separate: it gives a plain row a ghost counter.

## Quick start

From `bigodafny/fuzzing/`, with `bigodafny/.venv` active:

```bash
dotnet build -c Release DafnySteps          # after every .cs edit
dotnet test DafnySteps.Tests                # golden tests
scripts/demo.sh 2286_319 --run              # both passes and both traces on one row
python3 steptrace.py 1011_368               # steps on each stored test
python3 steptrace.py 1011_368 --trace       # plus steps at each program point
python3 stepfuzz.py 1011_368 --iters 300    # costliest input per size
```

`steptrace.py` builds `DafnySteps` only when it is missing. After a `.cs` edit,
rebuild it yourself.
