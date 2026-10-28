# 7. steptrace.py

Runs a row with a ghost `steps` counter on inputs, records `steps`, and checks
the bound in `Solve`'s `ensures`. By default it runs the row's proof copy in
`solutions-proved/`; `--dfy` runs any other file, such as `annotate`'s output.

## Usage

```bash
python3 steptrace.py SID                 # every stored test of the row
python3 steptrace.py SID --input FILE    # one input from a file
python3 steptrace.py SID --dfy FILE      # a different .dfy, e.g. annotate's output
python3 steptrace.py SID --dfy FILE --counter cost   # FILE's counter is `cost`, not `steps`
python3 steptrace.py SID --trace         # also steps at each program point
python3 steptrace.py SID --trace 37,42  # only points on lines 37, 42
python3 steptrace.py SID --trace loops   # only loop heads
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
- `bound`: the value of `E` in the first `ensures steps <= E`; absent when there is none.
  `steps / bound` falling as the input grows means the bound is loose.
- `--trace` is slow: every trace point costs two Python calls.
  `--trace LINE,..` compiles only the points on those lines; the others cost nothing.

## Screening proofs for loose bounds

A proof in `solutions-proved/` can be a class looser than its code: it holds, but
`steps` grows slower than the bound. This finds such proofs from stored tests only.

1. Run every verified proof on its stored tests; each writes `out/trace/<SID>.jsonl`
   with `steps` and `bound` per test (about 9 minutes for 321 proofs, 4 at a time):
   ```bash
   python3 -c "import json; [print(json.loads(l)['solution_id']) for l in open('../data/complexity_proofs.jsonl')]" \
     | xargs -P 4 -I{} python3 steptrace.py {} > /dev/null
   ```
2. Per proof, keep the costliest test in each doubling of `bound`, and fit
   `log(steps)` against `log(bound)` over those tests. Skip a proof with fewer than
   4 such tests or a bound range under 16x: its tests cannot tell.
3. A slope well below 1 (say under 0.8) means `steps` grows slower than the bound.
4. Read the flagged rows' Python. Most flags are tests that exit early or never
   reach the worst case (`1015_168` gets only even `n`); those proofs are fine.
   The rest are loose: prove the tight class and replace the copy.

On 2026-10-20 this rated 163 of 321 proofs, flagged 21, and 5 were loose (`5_100`,
`1011_368`, `2913_484`, `1820_180`, `2586_20`; `bigodafny/CHANGELOG.md`).
Run it again after new proofs land.
