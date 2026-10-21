# 9. Output files, tests, common problems

## Output files (not in git)

| Path | Written by | Contents |
|---|---|---|
| `.build/trace_<SID>*/` | `steptrace.py` | generated Python, `harness.py`, `points.json` |
| `out/trace/<SID>.jsonl` | `steptrace.py` | one result per input |
| `demo/<problem>/` | `scripts/demo.sh` | inputs and outputs of each tool |

## Tests

```bash
dotnet test DafnySteps.Tests                    # from fuzzing/
UPDATE_GOLDEN=1 dotnet test DafnySteps.Tests    # save new outputs as expected; check with git diff
```

- Each test runs `deghost` or `annotate` on one file in `cases/deghost/` or `cases/annotate/`.
- The output must match `<name>.expected.*` and must have no Dafny errors.
- When a test fails, the actual output stays next to it as `<name>.actual.*`.

## Common problems

| Problem | Fix |
|---|---|
| A `.cs` edit has no effect | `dotnet build -c Release DafnySteps` |
| `steptrace.py` cannot compile the row | read the Dafny error; a ghost error names a variable `deghost` missed |
| `bound_ok: false` on a guessed bound | the guess is too low; raise it |
| `bound_ok: false` on a verified proof | run `deghost` on the proof and look for a statement that now counts differently |
| Every result is `requires` | the inputs break the proof's `requires`; check them with `precheck.py` |
