# fuzzing/ — running ghost step counters

A prototype, not a gate. Open work is in `TODO-fuzzing.md`.

A proof copy in `solutions-proved/` counts work in a ghost `steps`. Compiling
erases ghost code, so the counter never runs. The code here makes it run.

Read `docs/` in order:

| File | Topic |
|---|---|
| `docs/01-overview.md` | the four tools, file layout, data flow, quick start |
| `docs/02-dafny-setup.md` | how Dafny is installed; how `DafnySteps` links against it |
| `docs/03-dafny-pipeline.md` | parse, resolve, verify, compile; parse tree vs resolved tree; ghost |
| `docs/04-dafny-plugins.md` | the plugin API, source ranges, the printer, the prelude |
| `docs/05-dafny-python.md` | what `dafny translate py` emits and how to call it |
| `docs/06-deghost.md` | `Deghost.cs`: ghost counter → compiled counter |
| `docs/07-steptrace.md` | `steptrace.py`: build, harness, `Runner`, statuses |
| `docs/08-stepfuzz.md` | `stepfuzz.py`: MAP-Elites search for costly inputs |
| `docs/09-annotate.md` | `Annotate.cs`, `CostModel.cs`: plain row → ghost counter |
| `docs/10-outputs-debugging.md` | where output goes; what to check when it fails |

`demo/` holds real `deghost` and `annotate` output for row `2286_319`.
