# 5. The Python that Dafny generates

```bash
dafny translate py row.dfy --no-verify --include-runtime --output DIR/out
# DIR/out-py/module_.py   the row
# DIR/out-py/_dafny/      Dafny's Python runtime library
```

- `module_.default__.Solve(args)` returns all compiled out-parameters as a tuple.
- After `deghost`, `Solve` returns `(output, steps)`.
- A Dafny `string` is a `_dafny.Seq` of `_dafny.CodePoint`; a `seq` is a `_dafny.Seq`.
- `validate.conv_expr` converts a Python value to the type in `data/signatures.jsonl`.
- `print id, steps;` becomes two calls to `_dafny.print`. `steptrace.py` replaces that function.
