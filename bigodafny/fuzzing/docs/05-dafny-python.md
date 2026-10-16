# 5. Dafny's Python output

```bash
dafny translate py row.dfy --no-verify --include-runtime --output DIR/out
# -> DIR/out-py/module_.py   the row's top-level declarations
# -> DIR/out-py/Prelude.py   the prelude module
# -> DIR/out-py/_dafny/      the runtime
```

## Calling `Solve`

- Top-level methods become static methods of `module_.default__`.
- `default__.Solve(args)` returns a tuple of the compiled out-parameters.
- After deghost, `Solve` ends with `return output, steps`; helpers likewise return `r, steps`.
- Locals are renamed: `a` becomes `d_0_a_`.

## Argument values

| Dafny type | Python runtime value |
|---|---|
| `int` | `int` |
| `bool` | `bool` |
| `real` | `_dafny.BigRational` |
| `string` | `_dafny.Seq` of `_dafny.CodePoint` |
| `seq<T>` | `_dafny.Seq` |
| tuple | Python tuple |

- `validate.conv_expr(dafny_type, expr)` builds the conversion expression.
- The parameter types come from the row's signature in `data/signatures.jsonl`.

## `print`

- `print a, b;` compiles to `_dafny.print(_dafny.string_of(a))`, then the same for `b`.
- The steptrace harness replaces both functions.
- So a trace point `print id, steps;` reaches the harness as two calls: id, then steps.
- A row's own `print` statements would collide with trace points; rows return `output` instead.
