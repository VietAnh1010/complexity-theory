# fuzzing/

Tools for finding a step bound for a row. A prototype; open work is in
`TODO-fuzzing.md`.

The loop:

1. `annotate` adds a ghost step counter `steps` to the row, with no bound.
2. `deghost` makes `steps` compiled code, so it runs.
3. `steptrace.py` runs it on the stored tests, or the `fuzz` tool (`experiments/fuzz/fuzz_mcp.py`) on inputs
   from a generator an agent writes, and records `steps` for each input size.
4. An LLM reads those numbers and guesses a bound; the bound goes into the row as an `ensures`.
5. Repeat from 2 until the bound is good enough. Each run also checks the current bound.

Read `docs/` in order:

| File | Contents |
|---|---|
| `01-overview.md` | the loop, tools, files, quick start |
| `02-dafny-setup.md` | the Dafny install and how `DafnySteps` uses it |
| `03-dafny-pipeline.md` | what `dafny` does with a file; ghost code |
| `04-dafny-plugins.md` | plugins, source ranges, the printer |
| `05-dafny-python.md` | the Python that Dafny generates |
| `06-deghost.md` | `deghost`: make `steps` compiled |
| `07-steptrace.md` | `steptrace.py`: run `steps` on inputs |
| `08-annotate.md` | `annotate`: add `steps` to a row |
| `09-outputs-debugging.md` | output files, tests, common problems |
