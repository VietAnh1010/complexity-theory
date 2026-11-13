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

- [ ] `annotate`: AlternativeStmt, match statements, `:-` calls stop it (no rule yet)
- [ ] Decide what to gather from a trace. The consumer is an LLM agent, so a
      log with an event per hit (millions of lines) is useless. Now: per
      point, hit count and min/max/last steps. `--trace LINE,..` compiles only
      the points on those lines.
      Open: what an agent needs (e.g. steps per loop iteration, against the
      invariant's bound), and how to gather it without paying one print per
      hit: `--trace` costs one Python call pair per event (`5_100`: 1.2 s
      untraced, 9.1 s traced, 14M events). A compiled stride was rejected as
      too complicated.
- [ ] Alternative, not explored: a per-call breakdown. A point's hit count sums
      over every call of its method, so it hides which call is costly when a
      helper runs on different sizes (`Fac2286(n)` and `Fac2286(k)`). Would
      record, per point, steps at each call's exit, grouped by call.
- [ ] (2026-10-21) `data/constraints.jsonl` quotes limits for few problems, so `fuzz`
      runs out-of-spec inputs for the rest.
- [ ] (2026-10-28) Fuzzing a proof means copying it into a directory named by its SID and rewriting
      its `include`, because `fuzz.py` takes the SID from the directory name. A `--sid` option would
      run the proof in place.
- [ ] (2026-10-28) A generator that holds a value the bound names fixed cannot show that term
      loose: `1915_158`'s agent kept gaps 57 bits wide. The brief should ask to grow every
      size and value in the bound.
- [ ] (2026-10-28) Compiled contracts run ghost functions: a ghost function that recurses twice per
      level (an early `MaxGapBits` in `1915_158`) makes every `fuzz` input time out.
- [ ] (2026-10-28) `1386_38` charges every running-gcd step its full depth, `O(n log max)`; the
      `1915_158` telescoping lemma gives `O(n + log max)`. It was rated by stored tests, not fuzzed.
- [ ] (2026-10-28) `proofs.py` runs 8 `dafny verify` at once (`common.WORKERS`) and can run out of
      memory; `proofs.run(workers=2)` finished in 15 minutes.
- [ ] (2026-10-26) `blind.py grade` assigns `guard.log` lines to rows by path, so a denial with no
      path (`true`, `echo skip`) voids nothing. Map the line's agent id to its row via `.locks/`.
- [ ] (2026-10-29) The `blind-guess` hook runs `$CLAUDE_PROJECT_DIR`'s `guard.py`, the main checkout's
      even for a session in a worktree, so a guard edited in a worktree never runs.
- [ ] (2026-10-29) `guard-path` is one file for every session: two sessions cannot run batches at once.
- [ ] (2026-10-29) `guard.py` fails open: when `guard-path` names a deleted directory, `log_denial`
      raises, the hook exits 1, and the call runs.
- [ ] (2026-10-29) A harmless call in the agent's own row (`cat row.dfy`) is denied and voids it.
- [ ] (2026-10-29) A row directory is named by its host, so a fabricated row looks like a real one,
      two arms of one row cannot share a batch, and `grade` compares with the host's label.
- [ ] (2026-10-21) `steptrace.py`: move `HARNESS` into its own file? It stays a template:
      the call to `Solve` (`{args}`) is code built from the row's signature. `--log` is gone
      (2026-10-28). Keep the CLI if the stored-test audit (`docs/07-steptrace.md`) is
      still wanted: undecided.
