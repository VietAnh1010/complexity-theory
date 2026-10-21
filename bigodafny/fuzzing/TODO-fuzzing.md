# TODO: step tracing and fuzzing

Prototype, in development. Nothing here is a gate. `bigodafny/`'s `CHANGELOG.md`,
`DOCS.md`, `README.md` and `STATUS.md` are not updated for this work until asked;
changes go in `fuzzing/CHANGELOG.md`.

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
- `steptrace.py` stays Python and builds through the plugin.

## State

- [x] `deghost`: CLI and plugin; trace points as `PrintStmt` nodes; Solve's
      contract compiled as `TraceRequires`/`TraceBound`
- [x] `steptrace.py` builds through the plugin; regex code removed
- [x] `annotate`: counter, charges per COMPLEXITY.md, call steps via a ghost lhs
- [x] `annotate` keeps the Python block of the row's header and nothing else
      of it (title, label, label-audit verdicts); the printer drops other comments
- [x] `annotate` stops on code outside the cost model; `enable=functions,seq`
      adds rules for row functions (`F_steps`) and `seq(n, i => e)`
- [x] Rule `arrays`; `let`, lambdas, tuple patterns, `assert P; e` in the table.
      A quantifier in compiled code is an error; `531_3456` and `1722_66` now
      recurse instead. With `enable=functions,seq,arrays`, 629 of 636 rows annotate.
- [ ] `var x :| P` stops `annotate` (5 rows). Decide per kind:
      - int-range search (`1453_483`, `1332_41`): rewrite as a loop, like the
        quantifiers, or charge it as a loop over the range?
      - pick from a set, `var x :| x in gg` (`976_1131`, `960_63`, `960_36`):
        cost 1, or `|gg|`? Under `|gg|`, a loop that empties a set by picking
        looks quadratic.
- [ ] Rows `2128_34`, `2826_42`: headers may still say the model has no arrays;
      `COMPLEXITY.md` now charges them.
- [ ] `annotate`: AlternativeStmt, match statements, `:-` calls stop it (no rule yet)
- [ ] `TraceBound` is `true` when Solve has no `ensures` (annotated rows)
- [x] `TraceBoundValue`: the value of `E` in the first `ensures steps <= E`;
      `steptrace.py` records it as `bound`
- [ ] Decide what to gather from a trace. The consumer is an LLM agent, so a
      log with an event per hit (millions of lines) is useless. Now: per
      point, hit count and min/max/last steps. `--trace LINE,..` compiles only
      the points on those lines; `--log FILE` writes events, capped at 10^5.
      Open: what an agent needs (e.g. steps per loop iteration, against the
      invariant's bound), and how to gather it without paying one print per
      hit: `--trace` costs one Python call pair per event (`5_100`: 1.2 s
      untraced, 9.1 s traced, 14M events). A compiled stride was rejected as
      too complicated.
- [x] `experiments/fuzz/fuzz_mcp.py` (`fuzz` tool): runs a generator's inputs (`GRID`, `FAMILIES`)
      untraced; per grid point, the costliest input's steps, bound,
      steps / bound, and loop-head hits from a loops-only rerun
- [x] Blind runs: `experiments/fuzz/blind.py` stages rows outside the repo;
      the `blind-guess` agent type (`.claude/agents/`) carries `guard.py` as its
      own PreToolUse hook, so only those agents are confined
- [ ] Alternative, not explored: a per-call breakdown. A point's hit count sums
      over every call of its method, so it hides which call is costly when a
      helper runs on different sizes (`Fac2286(n)` and `Fac2286(k)`). Would
      record, per point, steps at each call's exit, grouped by call.
- [ ] `annotate` refuses a row that already declares `steps` (`1387_34`, `1336_157`);
      `counter=NAME` works, but `steptrace.py` has no `--counter` yet
- [ ] (2026-10-21) `data/constraints.jsonl` quotes limits for few problems, so `fuzz`
      runs out-of-spec inputs for the rest.
- [ ] (2026-10-21) Concurrent `blind-guess` agents share one `fuzz` server; one agent ending
      closes it under another's call (`Connection closed`, `FINDINGS.md` batch `b10`).
      Undecided: a retry rule in `BRIEF.md` (not robust), back to a script the agent
      runs (needs Bash), or a Claude Code fix. Investigate before choosing.
- [ ] (2026-10-21) `fuzz` compiles the row 3 times per call: untraced, all points (to
      find the loops), loops only.
- [ ] (2026-10-21) `steptrace.py`: move `HARNESS` into its own file; drop `--log` and
      `LOG_CAP` (their only user, `./trace`, is gone). Keep the CLI if the stored-test
      audit (`docs/07-steptrace.md`) is still wanted: undecided.
