# 9. annotate (`Annotate.cs`, `CostModel.cs`)

Adds a ghost `steps` counter to a row that has none. Costs follow
`bigodafny/COMPLEXITY.md`.

## Usage

```bash
DafnySteps/bin/Release/net10.0/DafnySteps annotate IN.dfy OUT.dfy [counter=NAME]
```

- Prints a note on stderr for each cost that `COMPLEXITY.md` does not define.
- Exits with 1 if IN is missing, has errors, or already has a variable named `steps`.
- The output states no bound on `steps`. Adding the bound and its loop invariants is the proof's job.

## What it adds to each method

- An out-parameter `ghost steps: nat`, set to 0 at the start.
- `steps := steps + <cost>;` before each statement that costs something.
- At the start of each loop body: 1, plus the condition's cost for a `while`.
- After a `while`: the cost of the last, false condition.
- After a call to another method in the file: that method's `steps`.

## Costs (`CostModel.Of`)

| Expression | Cost |
|---|---|
| literal, variable | 0 |
| operator, index, update | 1 + operands |
| `a && b`, `a \|\| b` | 1 + a, + b only if b is evaluated |
| `s + t` on sequences | operands + `\|t\|` |
| `[a, b, c]` | elements + 1 per element |
| `m.Keys`, `m.Values` | `\|m\|` |
| prelude function | as in `COMPLEXITY.md`, e.g. `IntToString(x)` costs `Digits(x)` |
| the row's own function, comprehension, lambda | 1, with a note |

## Example

```dafny
// input                               // output
method C(n: int, k: int)               method C(n: int, k: int)
  returns (r: int)                       returns (r: int, ghost steps: nat)
{                                      {
                                         steps := 0;
  var fn := F(n);                        var fn, s0 := F(n);
                                         steps := steps + s0;
                                         steps := steps + 1;
  var fk := F(n - k);                    var fk, s1 := F(n - k);
                                         steps := steps + s1;
                                         steps := steps + 1;
  r := fn / fk;                          r := fn / fk;
}                                      }
```

Comments in the row, including its Python source, are not kept.
