# 10. Outputs and debugging

## Outputs

| Path | Written by | Contents |
|---|---|---|
| `.build/trace_<sid>*/` | `steptrace.py` | translated Python, `harness.py`, `points.json`, `dataclass.py` |
| `out/trace/<sid>.jsonl` | `steptrace.py` | per input: status, steps, `bound_ok`; per-point table with `--trace` |
| `out/fuzz/<sid>.json` | `stepfuzz.py` | elites with input text, seed bests, fits, ties, stats |
| `DafnySteps/bin/`, `obj/` | `dotnet build` | build output; git-ignored |

- `.build/` and `out/` are git-ignored.

## Debugging

| Symptom | Check |
|---|---|
| Scripts ignore a `.cs` edit | rebuild: `dotnet build -c Release fuzzing/DafnySteps` |
| Unsure what the plugin compiles | run `DafnySteps deghost` with the same arguments; same pass |
| Build fails | the logged Dafny error; a ghost error names a variable the analysis missed |
| `bound_ok: false` | diff `deghost` output against the proof: some statement counts differently |
| Every result is `requires` | inputs fall outside the proof copy's `requires`; check with `precheck.py` |
| `--trace` is slow | run without it for totals; each trace point costs two Python calls per hit |
| `annotate` output nearly empty, exit 0 | the input path is wrong; the missing file is reported but not fatal |
