# fuzzing/ — running ghost step counters

A prototype, not a gate. Open work is in `TODO-fuzzing.md`.

A proof copy in `solutions-proved/` counts work in a ghost `steps`. Compiling
erases ghost code, so the counter never runs. The code here makes it run.

Read `docs/` in order:

| File | Topic |
|---|---|
| `01-overview.md` | the tools, layout, data flow, quick start |
| `02-dafny-setup.md` | the Dafny install and how `DafnySteps` uses it |
| `03-dafny-pipeline.md` | parse, resolve, verify, compile; ghost code |
| `04-dafny-plugins.md` | the plugin API, source ranges, the printer |
| `05-dafny-python.md` | Dafny's Python output |
| `06-deghost.md` | ghost counter → compiled counter |
| `07-steptrace.md` | running a counter on inputs |
| `08-stepfuzz.md` | searching for costly inputs |
| `09-annotate.md` | plain row → row with a ghost counter |
| `10-outputs-debugging.md` | outputs, tests, debugging |
