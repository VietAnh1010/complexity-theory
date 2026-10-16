# 6. Deghost (`Deghost.cs`)

Makes a ghost step counter compiled, so it runs. `steptrace.py` applies it
as a Dafny plugin; the CLI prints the result so you can read it.

## Usage

```bash
DafnySteps/bin/Release/net10.0/DafnySteps deghost IN.dfy OUT.dfy [trace] [contracts] [points=P.json]
```

| Argument | Effect |
|---|---|
| `trace` | add `print <id>, steps;` after each update of `steps` and at each loop head |
| `contracts` | add `TraceRequires` and `TraceBound`: `Solve`'s `requires` and `ensures` as compiled checks |
| `points=P.json` | write each trace point's id, method, line and kind |

## What becomes compiled

Starting from each method's out-parameter `steps`, repeated until nothing changes:

- a variable assigned to something compiled;
- the `if`/`while` guards around that assignment;
- for `x, s := M(..)` with `s` compiled: `M`'s out-parameter in `s`'s position;
- an argument passed for a compiled parameter;
- a ghost function used by any of these, and the functions it calls.

Variables are matched by name within a method.

## Example

```dafny
// before                              // after `deghost ... trace`
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

- `TraceBound` skips an `ensures` that names a ghost output.
- With no `ensures`, `TraceBound` always returns true.
