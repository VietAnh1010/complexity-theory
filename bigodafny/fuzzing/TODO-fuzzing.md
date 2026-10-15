# TODO: step tracing and fuzzing

Prototype, in development. Nothing here is a gate. `CHANGELOG.md`, `DOCS.md`,
`README.md` and `STATUS.md` are not updated for this work until asked.

## Requirements

1. **Trace steps.** Run a Dafny row that carries ghost `steps` code and record
   the value of `steps` at different program points of the execution.
2. **Fuzz by a measurement.** Generate good inputs to feed the program for
   `steps`. Inputs are generated according to a measurement (an input size).
3. **Insert the ghost code mechanically.** A script takes a plain row and adds
   the ghost `steps` counter to it.
4. **Deghost mechanically.** A script takes a row with ghost `steps` code and
   makes that code compiled, so it runs.
5. **No text processing.** 3 and 4 work on Dafny's own AST, not on regexes over
   source text. Text processing is brittle.
6. **Deghost is both a tool and a plugin.** The plugin compiles the row; the
   tool prints the deghosted program so it can be read and tested.

## Design

- The AST is `DafnyCore` 4.11.0, Dafny's implementation. Its documented entry
  point is the plugin API (Dafny Reference Manual, "Plugins to Dafny"), which
  the manual calls experimental: the AST changes between Dafny versions. The
  tool is built against the pinned Dafny install.
- `DafnySteps/` (C#) builds one DLL: a CLI (`deghost`, `annotate`) and a
  plugin (`dafny ... --plugin "DafnySteps.dll,trace contracts points=P.json"`).
- `deghost` runs before resolution, so the CLI and the plugin share one pass.
  Flow into the counter is matched by name within a method; the resolver
  rejects the program if that misses a ghost value.
- `annotate` loads the file twice: the resolved copy decides charges (what a
  `+` or a call is), the parse-only copy is changed and printed. Nodes are
  matched by source range.
- `steptrace.py` and `stepfuzz.py` stay Python and build through the plugin.

## State

- [x] `deghost`: CLI and plugin; trace points as `PrintStmt` nodes; Solve's
      contract compiled as `TraceRequires`/`TraceBound`
- [x] `steptrace.py` builds through the plugin; regex code removed
- [x] `annotate`: counter, charges per COMPLEXITY.md, call steps via a ghost lhs
- [ ] `annotate` drops comments: the printer does not keep them, so a row's
      header (the Python source) is lost
- [ ] `annotate` charges a row's own functions 1 each, and `seq(n, f)` only `n`;
      each such charge is reported as a note
- [ ] `annotate`: AlternativeStmt, match statements, `:-` calls not charged
- [ ] `stepfuzz.py`: default size mixes lengths and values; use `--measure`
- [ ] `TraceBound` is `true` when Solve has no `ensures` (annotated rows)
- [ ] Decide what to gather from a trace. The consumer is an LLM agent, so a
      log with an event per hit (millions of lines) is useless. Now: per
      point, hit count and min/max/last steps, plus the first `--keep` events.
      Open: what an agent needs (e.g. steps per loop iteration, against the
      invariant's bound), and how to gather it without paying one print per
      hit: `--trace` costs one Python call pair per event (`5_100`: 1.2 s
      untraced, 9.1 s traced, 14M events). A compiled stride was rejected as
      too complicated.
- [ ] `annotate` refuses a row that already declares `steps` (`1387_34`);
      `counter=NAME` works, but `steptrace.py` has no `--counter` yet
