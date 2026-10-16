# 3. What `dafny` does with a file

```
parse → plugins → resolve → verify → compile
```

## Parse

- Reads the text into a syntax tree.
- Names are only strings (`NameSegment`); they do not point to declarations yet.
- In `x := M(a)`, Dafny does not yet know whether `M` is a method or a function.

## Resolve

- Connects each name to its declaration and gives every expression a type.
- Stores the results in extra fields on the same nodes:

| Field | Contents |
|---|---|
| `Expression.Resolved` | the expression after Dafny rewrites it |
| `BinaryExpr.ResolvedOp` | the exact operator, e.g. int `Add` or sequence `Concat` |
| `AssignStatement.ResolvedStatements` | plain assignments, or a `CallStmt` for a method call |

- Reports an error when compiled code reads a ghost value.

## Verify

- Proves the program correct with Z3.
- The tools here skip it (`--no-verify`); `proofs.py` verifies the proofs.

## Compile

- `dafny translate py` writes Python.
- Ghost code is deleted.

## Ghost code

- Each parameter, local variable and function has a ghost flag.
- `deghost` clears flags before resolution, so the resolver checks the result.
- If `deghost` misses a variable, Dafny reports an error; the program is never silently wrong.
