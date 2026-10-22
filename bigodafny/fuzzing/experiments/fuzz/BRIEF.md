# Name the tightest complexity class of `Solve`

Your working directory is `{{DIR}}`. Everything you need is in it.

## Rules

- Read and write files only in this directory. Write files with the Write tool.
- Do not look for the answer anywhere else: no other directory, no git, no web. A hook denies
  such calls and logs them, and a logged attempt voids the result.
- Do not prove anything, and do not edit `row.dfy`.

<!-- code -->

Do not run anything. Use Read, Glob and Grep; a hook denies Bash.

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

You can run the program with `fuzz`, one Bash command, typed exactly so:

```
{{FUZZ}} {{DIR}}/FILE.dfy {{DIR}}/gen.py [--per N]
```

Bash runs this command and nothing else. Give the Bash call `timeout: 600000`, and do not run it
in the background. Write `gen.py`:

```python
GRID = [{"n": 8}, {"n": 16}, ...]       # sizes, one dict per table row
FAMILIES = {"random": f, ...}           # f(rng, **sizes) -> input text, as on stdin
```

`gen.py` only builds input text: it must not read or write files or run other programs.
Stay inside the statement's limits: `fuzz` checks them only for some problems, and counts an
input it rejects as `out-of-spec`. `fuzz` on `row.dfy` and `gen.py` prints, per grid row, the
costliest input's `steps` and how often the busiest loops ran. To test a candidate bound E,
copy `row.dfy` to `round-k.dfy`, add `ensures steps <= E` to `Solve`, and run
`fuzz` on `round-k.dfy`: it also shows E and `steps / E`. A ratio that falls as sizes grow
means E is a looser class than the code; a flat ratio means the class fits; `BOUND BROKEN`
means E is too low. Write families for the inputs you think cost most, not only random ones.
Run `fuzz` at least once and at most 3 times, and base your answer on what it shows as well as on the code.

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

Write `class` in this form, with no spaces: `O(1)`, `O(logn)`, `O(n)`, `O(nlogn)`,
`O(n**2)`, `O(n*m)`, `O(n+mlogm)`. Powers take `**`, products `*`, and `log` follows its
factor with no `*` or brackets. Call the main measure `n` and a second one `m`, and define
them in `measures`.

Write `worst_case` and `reasoning` for a reader who knows the Python in `row.dfy`'s header
but not the problem: name its variables and loops ("the outer loop runs once per query and
sorts `a` each time"), not the statement's story. `example` is one concrete input,
small enough to read.

Your final message: one line, the class and its measures.

## Problem statement

{{STATEMENT}}
