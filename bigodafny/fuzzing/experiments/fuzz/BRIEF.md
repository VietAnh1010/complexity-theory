# Name the tightest complexity class of `Solve`

Your working directory is `{{DIR}}`. It holds everything you need, except the shared prelude
`{{PRELUDE}}`.

## Rules

- Read and write files only in this directory; you may also read `{{PRELUDE}}`. Write files
  with the Write tool.
- Do not look for the answer anywhere else: no other directory, no git, no web. A hook denies
  such calls and logs them, and a logged call voids your result.
- Do not prove anything, and do not edit `row.dfy`.

<!-- code -->

Do not run anything. Use Read, Glob and Grep; a hook denies Bash.

<!-- /code -->

## Files

| File        | Contents                                                                                                    |
| ----------- | ----------------------------------------------------------------------------------------------------------- |
| `row.dfy`   | `Solve`, the Python it was translated from (in its header), and a ghost counter `steps` that charges each operation |
| the prelude | the library functions `row.dfy` calls, and what each costs                                                  |

## Task

Give the tightest upper bound on `steps` over the worst inputs the problem statement allows,
as a complexity class over measures of the input: lengths, counts or values. Tightest means a
class you believe `steps` reaches on some family of inputs, not just a safe one. Count costs
the way `row.dfy` charges them, calls into the prelude included.

<!-- code -->

Work from the code alone.

<!-- /code -->

<!-- fuzz -->

You can run the program with `fuzz`. Bash runs this one command and nothing else:

```
{{FUZZ}} {{DIR}}/row.dfy {{DIR}}/gen.py [--per N] [--bound 'E']
```

Give the Bash call `timeout: 600000`, and do not run it in the background. First write
`gen.py`:

```python
GRID = [{"n": 8}, {"n": 16}, ...]       # sizes, one dict per table row
FAMILIES = {"random": f, ...}           # f(rng, **sizes) -> input text, as on stdin
```

`gen.py` only builds input text: it must not read or write files or run programs. Keep
inputs inside the statement's limits; `fuzz` checks them only for some problems, and marks
an input it rejects `out-of-spec`.

For each grid row, `fuzz` prints the costliest input's `steps` and how often the busiest
loops ran. Write families for the inputs you think cost most, not only random ones.

To test a candidate bound E, add `--bound 'E'`, with E a Dafny expression over `Solve`'s
parameters, in single quotes: `--bound '4 * |a_list| * |a_list| + 100'`. The table then also
shows E and `steps / E`:

- a ratio that falls as sizes grow: E is a looser class than the code;
- a flat ratio: the class fits;
- `BOUND BROKEN`: E is too low.

Run `fuzz` at least once and at most 3 times. Base your answer on its tables and on the code.

<!-- /fuzz -->

## Answer

Write `answer.json`:

```json
{
  "class": "O(nlogn)",
  "measures": "n = |a_list|",
  "worst_case": "the inputs that cost most",
  "example": "a small worst-case input, as on stdin",
  "reasoning": "two or three lines",
  "confidence": "high|medium|low"
}
```

<!-- fuzz -->

Also add `"skipped"`: each step you chose not to take, and why (`"did not test a bound: the
sort fixes O(nlogn)"`), or `"none"`.

<!-- /fuzz -->

Write `class` with no spaces, in this form: `O(1)`, `O(logn)`, `O(n)`, `O(nlogn)`, `O(n**2)`,
`O(n**1.5)`, `O(n*m)`, `O(n+mlogm)`. Powers take `**`, products `*`, and `log` follows its factor with no
`*` or brackets. Call the main measure `n` and a second one `m`, and define them in
`measures`.

Write `worst_case` and `reasoning` for a reader who knows the Python in `row.dfy`'s header but
not the problem. Name its variables and loops ("the outer loop runs once per query and sorts
`a` each time"), not the statement's story. `example` is one concrete input, small enough to
read.

End with one line: the class and its measures.

## Problem statement

{{STATEMENT}}
