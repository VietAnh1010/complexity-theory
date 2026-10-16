# 10. Outputs, tests, debugging

## Outputs (all git-ignored)

| Path | Written by |
|---|---|
| `.build/trace_<SID>*/` | `steptrace.py`: compiled Python, `harness.py`, `points.json` |
| `out/trace/<SID>.jsonl` | `steptrace.py` |
| `out/fuzz/<SID>.json` | `stepfuzz.py` |
| `demo/<problem>/` | `scripts/demo.sh` |

## Tests

```bash
dotnet test DafnySteps.Tests                    # from fuzzing/
UPDATE_GOLDEN=1 dotnet test DafnySteps.Tests    # accept the new outputs; review with git diff
```

- Each `cases/<pass>/<name>.dfy` runs through the CLI.
- Its output must equal `<name>.expected.*` and must resolve.
- A failure leaves `<name>.actual.*` beside it for diffing.

## Debugging

| Symptom | Check |
|---|---|
| A `.cs` edit has no effect | `dotnet build -c Release DafnySteps` |
| `steptrace.py` build fails | the Dafny error it prints; a ghost error names a missed variable |
| `bound_ok: false` | run `deghost` on the proof and compare: some statement counts differently |
| Every result is `requires` | the inputs break the proof's `requires`; check with `precheck.py` |
