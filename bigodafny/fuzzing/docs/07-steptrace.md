# 7. steptrace.py

Runs a row's step counter on inputs.

## Usage

```bash
python3 steptrace.py SID                 # every stored test of the row
python3 steptrace.py SID --input FILE    # one input
python3 steptrace.py SID --dfy FILE      # another .dfy, e.g. annotate's output
python3 steptrace.py SID --trace         # also steps at each program point
```

Writes `out/trace/<SID>.jsonl`.

## Steps

1. Compile the proof copy with the `deghost` plugin into `.build/trace_<SID>*/`.
   If the contract checks fail to compile, compile again without them.
2. Start `harness.py` there: one long-lived Python process that runs `Solve`.
3. For each input: parse it with the row's `Input.from_str`, check
   `TraceRequires`, run `Solve`, check `TraceBound`.

## Result status

| Status | Meaning |
|---|---|
| `ok` | ran; `steps` recorded |
| `requires` | the input is outside the proof's `requires` |
| `parse` | `Input.from_str` failed |
| `timeout` | over the time limit (default 30 s) |
| `error` | `Solve` raised |

- `bound_ok: false` means the compiled counter exceeded the proved bound: a `deghost` bug.
- `--trace` is slow: every trace point is two Python calls.
