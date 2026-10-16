# 9. annotate (`Annotate.cs`, `CostModel.cs`, `CostRules.cs`)

Adds a ghost `steps` counter to a row that has none. Costs follow
`bigodafny/COMPLEXITY.md`.

## Usage

```bash
DafnySteps/bin/Release/net10.0/DafnySteps annotate IN.dfy OUT.dfy [counter=NAME] [enable=functions,seq,arrays]
```

- By default it charges only what `COMPLEXITY.md`'s table covers.
- Any other code stops it with an error that names the code and its line.
- `enable=` turns on extra rules for code outside the table (below).
- Exits with 1 if IN is missing, has errors, contains code it cannot charge,
  or already has a variable named `steps`.
- The output states no bound on `steps`. Adding the bound and its loop invariants is the proof's job.

## Rules

| Rule | Charges |
|---|---|
| `functions` | a call `F(x)` to the row's own function: `F_steps(x)` |
| `seq` | `seq(n, i => e)`: `(1 + k) * n` if `e` costs a constant `k`; else `n + SumSeq(seq(n, i => <cost of e>))` |
| `arrays` | `new T[n]`: `n`; `new T[n, m]`: `n * m`; `new T[n](i => e)`: as `seq`; `new T[] [a, b]`: as a display |

For `functions`, `annotate` adds `ghost function F_steps` after each function
`F` in the file, with `F`'s parameters, `requires` and `decreases`. Its body is
the cost of `F`'s body; a recursive call costs `F_steps` again.

To add a rule: write a class implementing `ICostRule` in `CostRules.cs`, and
add its name to `Annotate.Rules` and `Annotate.RuleFor`.

## What it adds to each method

- An out-parameter `ghost steps: nat`, set to 0 at the start.
- `steps := steps + <cost>;` before each statement that costs something.
- At the start of each loop body: 1, plus the condition's cost for a `while`.
- After a `while`: the cost of the last, false condition.
- After a call to another method in the file: that method's `steps`.

## Costs without rules (`CostModel.Of`)

| Expression | Cost |
|---|---|
| literal, variable | 0 |
| operator, index, update | 1 + operands |
| `a && b`, `a \|\| b` | 1 + a, + b only if b is evaluated |
| `if c then x else y` | 1 + c + the branch taken |
| `var x := e; body` | e + body |
| `var (a, b) := e;` | e |
| a lambda | 0; its body is charged where it is called |
| `assert P; e` | e |
| `s + t` on sequences | operands + `\|t\|` |
| `[a, b, c]` | elements + 1 per element |
| `m.Keys`, `m.Values` | `\|m\|` |
| prelude function | as in `COMPLEXITY.md`, e.g. `IntToString(x)` costs `Digits(x)` |
| `forall`/`exists` in compiled code | error; write a loop instead |
| anything else | error |

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
