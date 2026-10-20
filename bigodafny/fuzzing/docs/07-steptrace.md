# 7. steptrace.py

Runs a row with a ghost `steps` counter on inputs, records `steps`, and checks
the bound in `Solve`'s `ensures`. By default it runs the row's proof copy in
`solutions-proved/`; `--dfy` runs any other file, such as `annotate`'s output.

## Usage

```bash
python3 steptrace.py SID                 # every stored test of the row
python3 steptrace.py SID --input FILE    # one input from a file
python3 steptrace.py SID --dfy FILE      # a different .dfy, e.g. annotate's output
python3 steptrace.py SID --trace         # also steps at each program point
python3 steptrace.py SID --trace 37,42 --log ev.tsv   # only points on lines 37, 42; log each event
```

Results go to `out/trace/<SID>.jsonl`.

## How it works

1. Compiles the file to Python with the `deghost` plugin, into `.build/trace_<SID>*/`.
   If the `contracts` checks do not compile, it compiles again without them.
2. Starts `harness.py`, one Python process that stays open and runs `Solve`.
3. For each input: parses it with the row's `Input.from_str`, checks
   `TraceRequires`, runs `Solve`, checks `TraceBound`.

## Status of each run

| Status | Meaning |
|---|---|
| `ok` | finished; `steps` recorded |
| `requires` | the input breaks the proof's `requires` |
| `parse` | `Input.from_str` failed |
| `timeout` | took longer than the limit (30 s by default) |
| `error` | `Solve` raised an exception |

- `bound_ok: false`: `steps` exceeded the bound in `ensures`.
  - For a guessed bound: the guess is too low.
  - For a verified proof: a `deghost` bug, since the compiled `steps` should match the proof's.
- With no `ensures`, `bound_ok` is always true.
- `--trace` is slow: every trace point costs two Python calls.
  `--trace LINE,..` compiles only the points on those lines; the others cost nothing.
- `--log FILE` writes one line per event, `test point steps`, up to 100,000 events.
