# 7. steptrace.py

Runs a row's step counter on inputs and records `steps`.

## `build(sid, trace, dfy)`

- Input: the row's proof copy (`solutions-proved/` or `value-bounded/`), or `--dfy`.
- Runs `dafny translate py --no-verify --include-runtime --plugin DafnySteps.dll,...`.
- Output directory: `.build/trace_<sid>[_t][_file]/`; `_t` with `--trace`, `_file` with `--dfy`.
- First try: with `contracts`. If that fails to compile, retry without.
- A typical cause of that failure: a contract that names a ghost-only predicate.
- The failure text of each attempt is kept in `notes` and logged.
- Returns the Python directory, the trace points, and whether contracts compiled.

## The harness

- `HARNESS` is a template; `Runner` writes it to `harness.py` in the build directory.
- It loads the row's `Input` dataclass from `data/tasks.jsonl` (`dataclass_code`).
- Protocol: one JSON request per line on stdin, one JSON result per line on stdout.
- Per request:
  1. `Input.from_str(text)`;
  2. `TraceRequires(args)`, if contracts compiled;
  3. `Solve(args)` → `(output, steps)`;
  4. `TraceBound(args, output, steps)`, if contracts compiled.
- A `SIGALRM` timer enforces the timeout (default 30 s).
- Per trace point it keeps: hit count, min, max and last `steps`.
- `--keep N` also keeps the first N `(point, steps)` events.

## `Runner`

- Starts the harness once and keeps it running; each `run(text)` is one request.
- A fuzzer therefore pays Python start-up and imports once.
- `seeds()` gives the row's stored tests that keep the problem's limits (`data/constraints.jsonl`).

## Result statuses

| Status | Meaning |
|---|---|
| `ok` | ran; `steps`, `output_len`, `hits` present |
| `requires` | `TraceRequires` rejected the input |
| `parse` | `Input.from_str` raised |
| `timeout` | over the time limit |
| `error` | `Solve` raised |

- `bound_ok: false`: the compiled counter exceeded the proved bound.
- That means deghost changed what is counted; the proof itself is verified.
- An annotated file has no `ensures`, so its `bound_ok` is always true.

## Command line

```
steptrace.py SID [--input FILE] [--dfy FILE] [--trace] [--keep N]
```

- Prints one line per test, then with `--trace` a per-point table for the last test.
- Writes `out/trace/<sid>.jsonl`.
- `--trace` is slow: each trace point costs two Python calls per hit.
