# 8. stepfuzz.py

For each input size, searches for the input with the largest `steps`.

## Usage

```bash
python3 stepfuzz.py SID [--iters N] [--seconds S] [--measure EXPR]
```

- `--measure`: the size, as a Python expression over the parsed input `i` (`"len(i.a)"`).
- Default size: each list's or string's length plus each int that is not a length.
- Writes `out/fuzz/<SID>.json`.

## Search

1. Learn the input's shape from the stored tests: value ranges, alphabets,
   and length relations such as `n == len(a)`.
2. Group inputs by size, two buckets per doubling; each keeps its costliest input.
3. Repeat: take a bucket's input, mutate it (grow, shrink, sort, reverse, …),
   restore the length relations, keep it if it costs more than its bucket's.

A new input is dropped if it does not parse back to the same value, is larger
than every stored test, breaks the problem's limits, or fails `TraceRequires`.

## Output

- Per bucket: size, best stored test's steps, best fuzzed steps, their ratio.
- `*` marks a bucket where a fuzzed input won.
- `fit_*`: growth classes ranked by how well `c·f(size) + d` fits the steps.
