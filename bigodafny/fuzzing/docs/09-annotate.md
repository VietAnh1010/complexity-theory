# 9. Annotate (`Annotate.cs`, `CostModel.cs`)

Adds a ghost step counter to a plain row, charged per `bigodafny/COMPLEXITY.md`.

## Usage

```bash
DafnySteps/bin/Release/net10.0/DafnySteps annotate IN.dfy OUT.dfy [counter=NAME]
```

- Notes go to stderr: each charge the model does not cover.
- Exit 1 when IN is missing, does not resolve, or already declares the counter.
- The output resolves but does not verify; invariants are still the prover's work.

## What it adds

- `ghost steps: nat` as an out-parameter, and `steps := 0;` first.
- `steps := steps + <cost>;` before each statement that costs something.
- In each loop body: 1, plus the guard for a `while`; after a `while`, the last guard.
- After a call to another annotated method: that method's steps.

## Charges (`CostModel.Of`)

| Expression | Cost |
|---|---|
| literal, variable | 0 |
| operator, index, update | 1 + operands |
| `a && b`, `a \|\| b` | 1 + a + b only when b runs |
| `s + t` on sequences | operands + `\|t\|` |
| `[a, b, c]` | elements + 1 per element |
| `m.Keys`, `m.Values` | `\|m\|` |
| prelude function | `COMPLEXITY.md`'s charge, e.g. `IntToString(x)` → `Digits(x)` |
| row's own function, comprehension, lambda | 1, with a note |

## Example

```dafny
// before                              // after
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

The row's comments, including its Python source, are lost.
