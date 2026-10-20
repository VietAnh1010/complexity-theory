# Find and prove the tightest step bound

Your working directory is `{{DIR}}`. Everything you need is in it.

## Rules

- Start every Bash command with `cd {{DIR}} &&`. Read and write files only in this directory.
  Write files with the Write tool, not shell heredocs, and check each write landed.
- Do not look for the answer anywhere else: no other directory, no git, no web. A hook denies
  such calls and logs them, and a logged attempt voids the result.
- Do not change what the program computes. A proof may add only ghost code: lemmas, ghost
  functions, `assert`s, loop invariants, `ensures` on helpers, `decreases` clauses.
- Do not change the `steps` charges. They follow a fixed cost model and are already in `row.dfy`.
- No `assume`, no `{:axiom}`, no `decreases *` in a proof.

## Files

| File | Contents |
|---|---|
| `statement.txt` | the problem statement, with its input format and limits |
| `row.dfy` | `Solve` (with the Python it was translated from in its header) and a ghost counter `steps` |
| `prelude.dfy` | library functions and lemmas `row.dfy` uses (sorting, digits, output length) |
| `fuzz` | `./fuzz FILE.dfy gen.py [--per N]`: runs your generator's inputs on FILE, prints a table |
| `trace` | `./trace FILE.dfy INPUT.txt LINE,LINE`: runs one input, logs `steps` at those source lines |

## Task

Find the tightest upper bound on `steps` that holds for every input the statement allows,
as an expression over measures of `Solve`'s inputs (lengths, values, counts). Then prove it.

1. **Guess from the code.** Before running anything, write `guess.md`: the measures, the
   bound, its class (e.g. `O(n log n)`, with what `n` is), and why. Do not edit it later.
2. **Write `gen.py`.** It defines
   ```python
   GRID = [{"n": 8}, {"n": 16}, ...]       # sizes, one dict per table row
   FAMILIES = {"random": f, ...}           # f(rng, **sizes) -> input text, as on stdin
   ```
   Write families for the inputs you think cost most, not only random ones. Stay inside the
   statement's limits; `fuzz` skips inputs outside them. Use sizes up to the limits when a
   run takes seconds, not minutes.
3. **Round k.** Copy `row.dfy` to `round-k.dfy` and add the bound as Solve's first `ensures`:
   `ensures steps <= E`. `E` may call ghost functions you define in that file; they run as
   compiled code, so keep their recursion depth small (e.g. recurse on `x / 2`, not `x - 1`).
   Run `./fuzz round-k.dfy gen.py`. For each grid row it prints the costliest input's
   `steps`, the value of `E`, `steps / E`, and how many times the busiest loops ran.
   - `BOUND BROKEN`: E is too low, or a family you did not expect costs more. Fix and rerun.
   - `steps / E` falling as the sizes grow: E is a looser class than the code. Tighten it.
   - `steps / E` roughly constant: E has the right class. Stop.
   Use `./trace` on an input from `run-round-k/worst/` to see the loop counts that explain a row.
   Write each round's bound and what the table showed in `rounds.md`.
4. **Prove it.** Copy the last round's file to `verify-1.dfy`, add invariants and lemmas, and
   run `dafny verify verify-1.dfy`. Save each attempt as a new file `verify-<n>.dfy`. The proof
   must hold for every int the signature allows, not only inside the statement's limits; widen
   the constant or use `AbsInt` if needed, but keep the class. If the class you measured cannot
   be proved, you may prove a looser one; say so.

Budget: at most 3 rounds and 3 proof attempts. After the third failed attempt, stop:
record the proof as `unresolved` with the obstacle and write `record.json`.

## Report

Write `record.json`:

```json
{"g0": {"bound": "...", "class": "...", "measures": "..."},
 "final": {"bound": "...", "class": "...", "ratio_trend": "flat at 0.9"},
 "rounds": 2,
 "proof": {"status": "proved|unresolved", "file": "verify-3.dfy", "attempts": 3,
           "bound": "...", "class": "...", "obstacle": "null, or the invariant or lemma that would not go through"},
 "notes": "anything about the tools that got in your way"}
```

Your final message: at most 6 lines, the classes for g0, final and proof.
