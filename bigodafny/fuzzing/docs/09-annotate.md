# 9. Annotate (`Annotate.cs`, `CostModel.cs`)

Adds a ghost step counter to a plain row, charged per `bigodafny/COMPLEXITY.md`.
Sample output: `demo/2286_319.annotate.dfy`.

## Two loads

- The resolved copy says what each node is: int `+` vs sequence `+`, method vs function call.
- The parsed copy is edited and printed (`docs/04-dafny-plugins.md` § The printer).
- `resolvedByRange` and `parsedByRange` index both trees by source range.
- A statement with no resolved twin is not charged, and a note says so.

## What each compiled method gains

- An out-parameter `ghost steps: nat`, and `steps := 0;` as the first statement.
- `steps := steps + <cost>;` before each statement whose own expressions cost something.
- First in each loop body: 1, plus the guard for a `while`.
- After a `while`: the guard's final, failing evaluation.
- A call to another annotated method: `x := M(..)` → `x, s0 := M(..); steps := steps + s0;`.
- A `return` gains `steps` as an extra returned value.
- A method that already declares `steps` is refused; pass `counter=NAME`.

## The cost model (`CostModel.Of`)

| Expression | Cost |
|---|---|
| literal, variable | 0 |
| operator, index, update, member | 1 + operands |
| `a && b`, `a \|\| b`, `==>` | 1 + a + (b only when it runs) |
| `s + t` on sequences | operands + `\|t\|` |
| `if t then x else y` | 1 + t + the branch taken |
| `[a, b, c]` and other displays | elements + 1 per element |
| `m.Keys`, `m.Values`, `m.Items` | `\|m\|` |
| `seq(n, f)` | `n`; `f`'s cost not counted (noted) |
| prelude function | `COMPLEXITY.md`'s charge, e.g. `IntToString(x)` → `Digits(x)`, `Sort(s)` → `SortCost(\|s\|)` |
| the row's own function | 1 (noted) |
| comprehension, lambda, `let`, `match` | 1 (noted) |

- A cost is a constant plus expression terms (`Cost`); terms are copied from the parse tree.
- A term whose parse-tree node is missing is charged 1, and a note says so.

## Notes

- Notes go to stderr, one per line: `FILE: line N: <what was not modelled>`.
- An empty notes list means every charge came from the model.

## Example (`2286_319`)

Plain row:

```dafny
method C2286(n: int, k: int) returns (r: int)
{
  var fn := Fac2286(n);
  var fk := Fac2286(k);
  var fnk := Fac2286(n - k);
  r := fn / (fk * fnk);
}
```

Annotated:

```dafny
method C2286(n: int, k: int)
    returns (r: int, ghost steps: nat)
{
  steps := 0;
  var fn, s3 := Fac2286(n);
  steps := steps + s3;
  var fk, s4 := Fac2286(k);
  steps := steps + s4;
  steps := steps + 1;              // n - k
  var fnk, s5 := Fac2286(n - k);
  steps := steps + s5;
  steps := steps + 2;              // / and *
  r := fn / (fk * fnk);
}
```

(The `//` comments are added here; the printer emits none.)

## Limits

- The output resolves but does not verify; invariants and the bound are the prover's work.
- Not charged: alternative (`if case`) statements, `match` statements, `:-` calls.
- The row's header comment (its Python source) is lost.
