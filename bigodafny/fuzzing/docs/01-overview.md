# 1. Overview

## The loop

```
row.dfy                            the row: no step counter
   │  annotate
   ▼
row with ghost steps               no bound yet
   │  deghost
   ▼
row with compiled steps            Solve returns (output, steps)
   │  steptrace.py, or fuzz.py with an agent-written generator
   ▼
steps per input size               statistics
   │  LLM guesses a bound
   ▼
row with ghost steps + ensures     the guessed bound
   │  deghost → run → LLM → …
   ▼
repeat until the bound is good enough
```

From the second round on, every run checks the current bound (`TraceBound`).
An input that breaks it shows the guess is too low.

## Status of each step

| Step | Tool | Status |
|---|---|---|
| add a ghost counter | `DafnySteps annotate` | works; stops on code outside the cost model unless a rule is enabled (08) |
| make it run | `DafnySteps deghost` | works |
| run on stored tests | `steptrace.py --dfy FILE` | works on any file |
| run on generated inputs | `experiments/fuzz/fuzz.py` | works; the agent writes the generator; a call starts no input after 300 s |
| guess a bound | LLM | not built |
| check the bound | `TraceBound` | works; absent when there is no `ensures` |

## Tools

| Tool | Purpose |
|---|---|
| `DafnySteps annotate` | Adds a ghost `steps` counter to a row (08) |
| `DafnySteps deghost` | Turns `steps` into compiled code; `steptrace.py` uses it as a plugin (06) |
| `steptrace.py` | Runs the row on inputs, records `steps`, checks the bound (07) |

## Files

```
fuzzing/
  steptrace.py          runs a row's counter on inputs
  experiments/fuzz/     blind guess-only runs; fuzz.py runs an agent-written generator
  scripts/demo.sh       runs annotate, deghost and steptrace on one row -> demo/<problem>/
  DafnySteps/           C# code for annotate and deghost; a CLI and a Dafny plugin
  DafnySteps.Tests/     tests for DafnySteps
  Directory.Build.props path to the Dafny install
  TODO.md               open work
```

## Quick start

Run from `bigodafny/fuzzing/`, with `bigodafny/.venv` active:

```bash
dotnet build -c Release DafnySteps          # rebuild after every .cs edit
dotnet test DafnySteps.Tests                # run the tests
scripts/demo.sh 2286_319 --run              # annotate, deghost and steptrace on one row
```

One round of the loop on row `2286_319`:

```bash
DafnySteps/bin/Release/net10.0/DafnySteps annotate ../solutions/2286/2286_319.dfy counted.dfy enable=functions,seq,arrays
python3 steptrace.py 2286_319 --dfy counted.dfy    # steps on each stored test
```

`steptrace.py` builds `DafnySteps` only if it is missing. After editing a
`.cs` file, rebuild it yourself.
