# 5. Dafny's Python output

```bash
dafny translate py row.dfy --no-verify --include-runtime --output DIR/out
# DIR/out-py/module_.py   the row
# DIR/out-py/_dafny/      the runtime
```

- `module_.default__.Solve(args)` returns the compiled out-parameters as a tuple.
- After `deghost`, that tuple is `(output, steps)`.
- A Dafny `string` is a `_dafny.Seq` of `_dafny.CodePoint`; a `seq` is a `_dafny.Seq`.
- `validate.conv_expr` converts a Python value to the Dafny type in `data/signatures.jsonl`.
- `print id, steps;` becomes two `_dafny.print` calls; `steptrace.py` replaces that function.
