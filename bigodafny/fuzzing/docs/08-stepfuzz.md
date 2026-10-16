# 8. stepfuzz.py

Searches, for each input size, for the input with the largest `steps`.
Uses `steptrace.Runner` to run inputs.

## Input shape (`Shape`)

Learned from the row's stored tests, parsed with `Input.from_str`:

- per int path: the range of values seen;
- per string path: the alphabet and lengths seen;
- `views`: a `str` field that always holds integer tokens is mutated as an int or list of ints;
- `ties`: an int field always equal to a container's length plus a small offset (`n == len(a)`);
- `linked`: containers whose lengths are always equal.

## Size

- `--measure EXPR`: a Python expression over the parsed `Input`, named `i`.
- Default (`Shape.default_measure`): sum of each container's length and each untied int's value.
- A list of containers counts its elements, so a grid's size is its cell count.
- The default mixes lengths and values; prefer `--measure` (`TODO-fuzzing.md`).

## Search (MAP-Elites)

- Buckets are fractions of a doubling of size: `--res 2` gives two per doubling.
- Each bucket keeps its costliest input, its elite.
- Seeds: the stored tests fill the buckets first.
- Each iteration:
  1. pick a random elite;
  2. mutate 1–3 fields: grow, shrink, sort, reverse, fill, shuffle, nudge a value;
  3. repair ties and linked lengths;
  4. keep the child if it beats its bucket's elite.
- Values stay within the ranges seen in the stored tests.

A child is discarded unless:

- its text parses back to the same `Input` (round trip);
- its size is at most the largest seed's;
- it keeps the problem's limits (`data/constraints.jsonl`);
- `TraceRequires` accepts it (status `ok`).

## Growth fit (`fit`)

- Fits `steps ≈ c·f(size) + d` by least squares for each class in `CLASSES`.
- Ranks classes by relative RMSE; lower is better.
- Done separately for seed bests and for elites.
- `CLASSES` has no `O(sqrt n)`; a √n row is reported as `O(n)` with a large error.

## Command line

```
stepfuzz.py SID [--measure EXPR] [--iters N] [--seconds S] [--res R] [--seed K]
```

- Table columns: size, best seed steps, best fuzzed steps, their ratio.
- `*` marks a bucket a fuzzed input won.
- Writes `out/fuzz/<sid>.json`: elites with input text, seed bests, fits, ties, stats.
