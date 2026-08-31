# bigodafny

A Python -> Dafny translation dataset built from BigO(Bench)'s
`time_complexity_test_set`, keeping BigOBench's inferred time complexity label
attached to every row.

## Why the dataclass matters

639 of the 640 BigOBench solutions are stdin scripts:

```python
n = int(input())
a = list(map(int, input().split()))
...
print(ans)
```

There is no function, so there is no signature to translate. The one typed
argument list in the data is `dataclass_code` -- an `Input` dataclass that
BigOBench generated so its profiler could scale inputs:

```python
@dataclass
class Input:
    n: int
    a_list: List[int]
```

That is dead weight if you are only consuming the benchmark, and it is the
whole foundation here. `signature.py` turns it into:

```dafny
method Solve(n: int, a_list: seq<int>) returns (output: string)
```

309 of 311 problems map. The 2 that do not are recorded with the reason (a bare
`list` annotation with no element type), never guessed.

## How a row is judged

Compile, then diff. No specs and no `dafny verify` gate.

```
solutions/<pid>/<sid>.dfy
   |  dafny translate py --include-runtime
   v
out-py/module_.py  ->  Solve(...)
                            ^
                            |  Input.from_str(stdin)   <- BigOBench's own parser
                       stored test input
                            |
                     stdout  ==  stored expected output
```

Reusing `Input.from_str` rather than writing a Dafny stdin parser is what keeps
the typed method boundary. The Dafny side is pure computation.

## The split is measured, not read

Running the **original Python** against its own stored tests, only **540 of 640**
reproduce the expected output byte-for-byte. Codeforces accepted many of these
under a token-based or special checker, so the stored output is one accepted
answer, not the only one.

That 540 is the ceiling for any translation, so it defines the split:

| split | rows | meaning |
|---|---|---|
| `strict` | 540 | the Python matches exactly; a translation can be held to it |
| `loose` | 100 | it does not -- kept and labelled, never scored by byte-diff |

A regex over the problem statement ("if there are several solutions, print any
of them") predicts this badly: precision 0.38, recall 0.45. It is retained as
`nondet_hint` and gates nothing.

## Usage

```bash
dotnet tool install -g dafny --version 4.11.0
pip install z3-solver==4.12.1.0 numpy

python3 cli.py all                     # extract, signatures, scaffold, baseline, dataset
python3 cli.py validate --only 5_100   # one solution
python3 cli.py validate --generated    # all of them, largest test tier
python3 cli.py selftest                # prove the validator rejects bad translations
```

## Layout

| Path | What |
|---|---|
| `cli.py` | subcommands |
| `extract.py` | download + project into `data/tasks.jsonl` |
| `signature.py` | `dataclass_code` -> Dafny signature, via `ast` |
| `scaffold.py` | `.dfy` stubs; never clobbers a real body |
| `baseline.py` | runs the original Python; defines the split |
| `validate.py` | `dafny translate` + stdout diff |
| `dataset.py` | joins everything into `data/dataset.jsonl` + `stats.json` |
| `selftest.py` | asserts wrong answers are `fail` and syntax errors are `build` |
| `prelude.dfy` | `FloorDiv`, `IntToString`, `Join`, `SplitWs`, merge sort |
| `solutions/` | one `.dfy` per solution -- the authoring surface |

`data/tasks.jsonl` (79 MB) and `.cache/` are gitignored and regenerable;
`data/index.jsonl` is the committed manifest.

## prelude.dfy

Verifies clean (10 verified, 0 errors) and every helper is cross-checked against
CPython:

- `FloorDiv`/`FloorMod` -- 1458/1458 cases agree with Python `//` and `%`.
  Dafny's own `/` is Euclidean and disagrees whenever the divisor is negative.
- `IntToString` matches `str()`, `SortInts` matches `sorted()` on 200 random
  cases, `SplitWs` matches `str.split()`.

## Status

The pipeline is complete and proven end-to-end. Translations are not: 5 are
hand-written, the rest are stubs. Choosing a translator is deliberately a
separate decision -- see `../STATUS.md`.
