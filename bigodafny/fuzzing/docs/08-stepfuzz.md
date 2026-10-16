# 8. stepfuzz.py

Finds, for each input size, the input with the largest `steps`.

By default it runs the row's proof copy in `solutions-proved/`; `--dfy` runs
any other file, such as `annotate`'s output.

## Usage

```bash
python3 stepfuzz.py SID [--dfy FILE] [--iters N] [--seconds S] [--measure EXPR]
```

- `--measure` sets the input size: a Python expression over the parsed input `i`, e.g. `"len(i.a)"`.
- Default size: the length of each list and string, plus each int that is not a length.
- Results go to `out/fuzz/<SID>.json`.

## How it works

1. Reads the stored tests to learn the input format: value ranges, characters
   used, and length rules such as `n == len(a)`.
2. Sorts inputs into size groups, two per doubling of size. Each group keeps its costliest input.
3. Repeats: copies a group's input, changes it (longer, shorter, sorted,
   reversed, …), fixes the length rules, and keeps it if it costs more.

A new input is discarded if it does not parse back to the same value, is
larger than every stored test, breaks the problem's limits, or fails
`TraceRequires`.

## Output

- One line per size group: size, best stored test's `steps`, best new input's `steps`, ratio.
- `*` marks a group where a new input beat every stored test.
- `fit_*` lists growth classes, best first, by how well `c·f(size) + d` matches `steps`.
