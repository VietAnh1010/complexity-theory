# Name the tightest complexity class of `Solve`

Your working directory is `{{DIR}}`. Everything you need is in it.

## Rules

- Read and write files only in this directory. Write files with the Write tool.
- Do not look for the answer anywhere else: no other directory, no git, no web. A hook denies
  such calls and logs them, and a logged attempt voids the result.
- Do not prove anything, and do not edit `row.dfy`.

<!-- code -->

Do not run anything: do not call the `fuzz` tool. Use Read, Glob and Grep.

<!-- /code -->

## Files

| File            | Contents                                                                                                               |
| --------------- | ---------------------------------------------------------------------------------------------------------------------- |
| `row.dfy`       | `Solve` (with the Python it was translated from in its header) and a ghost counter `steps` that charges each operation |
| `prelude.dfy`   | library functions `row.dfy` calls, and what each costs                                                                 |

## Task

Give the tightest upper bound on `steps` over the worst inputs the problem statement (below) allows, as a
complexity class over measures of the input: lengths, counts, or values. Tightest means a
class you believe `steps` actually reaches on some family of inputs, not just one that is safe.
Count costs the way `row.dfy` charges them, including calls into the prelude.

<!-- code -->

Work from the code alone.

<!-- /code -->

<!-- fuzz -->

You can run the program with the `fuzz` tool: `fuzz(dfy, gen, per)`, with the absolute paths of a
`.dfy` file and `gen.py` in this directory. Write `gen.py`:

```python
GRID = [{"n": 8}, {"n": 16}, ...]       # sizes, one dict per table row
FAMILIES = {"random": f, ...}           # f(rng, **sizes) -> input text, as on stdin
```

`gen.py` only builds input text: it must not read or write files or run other programs.
Stay inside the statement's limits. `fuzz` on `row.dfy` and `gen.py` returns, per grid row, the
costliest input's `steps` and how often the busiest loops ran. To test a candidate bound E,
copy `row.dfy` to `round-k.dfy`, add `ensures steps <= E` to `Solve`, and run
`fuzz` on `round-k.dfy`: it also shows E and `steps / E`. A ratio that falls as sizes grow
means E is a looser class than the code; a flat ratio means the class fits; `BOUND BROKEN`
means E is too low. Write families for the inputs you think cost most, not only random ones.
Call `fuzz` at least once and at most 3 times, and base your answer on what it shows as well as on the code.

<!-- /fuzz -->

## Answer

Write `answer.json`:

```json
{
  "class": "O(n log n)",
  "measures": "n = |a_list|",
  "worst_case": "the inputs that cost most, in one line",
  "reasoning": "two or three lines",
  "confidence": "high|medium|low"
}
```

Your final message: one line, the class and its measures.

## Problem statement

{{STATEMENT}}
