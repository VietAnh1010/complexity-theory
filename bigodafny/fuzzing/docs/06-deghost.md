# 6. deghost (`Deghost.cs`)

Turns the ghost `steps` counter into compiled code, so it runs. `steptrace.py`
uses it as a Dafny plugin. The CLI writes the result to a file for reading.

## Usage

```bash
DafnySteps/bin/Release/net10.0/DafnySteps deghost IN.dfy OUT.dfy [trace] [contracts] [points=P.json]
```

| Argument | Effect |
|---|---|
| `trace` | adds `print <id>, steps;` after each change to `steps` and at the start of each loop body |
| `contracts` | adds `TraceRequires` and `TraceBound`, which check `Solve`'s `requires` and `ensures` at run time |
| `points=P.json` | writes the id, method, line and kind of each `print` added by `trace` |

## What becomes compiled

`deghost` starts with each method's out-parameter `steps` and repeats until
nothing new is added:

- a variable whose value is assigned to compiled code;
- the `if` and `while` conditions around that assignment;
- in `x, s := M(..)` with `s` compiled: `M`'s out-parameter in the same position;
- an argument passed to a compiled parameter;
- a ghost function used by any of these, and the functions it calls.

Variables are matched by name inside one method.

## Example

```dafny
// input                               // output of `deghost ... trace`
method F(x: int)                       method F(x: int)
  returns (p: int, ghost steps: nat)     returns (p: int, steps: nat)
{                                      {
  steps := 1;                            steps := 1;
                                         print 0, steps;
  while i <= x {                         while i <= x {
                                           print 1, steps;
    p := p * i;                            p := p * i;
    steps := steps + 4;                    steps := steps + 4;
                                           print 2, steps;
  }                                      }
}                                      }
```

- `TraceBound` leaves out an `ensures` that mentions a ghost out-parameter.
- If `Solve` has no `ensures`, `TraceBound` always returns true.
