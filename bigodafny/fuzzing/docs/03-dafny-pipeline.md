# 3. Inside `dafny`

```
parse → [plugin] → resolve → verify → compile
```

## Parse

- Produces a syntax tree; names are still plain strings (`NameSegment`).
- `x := M(a)` is an `AssignStatement`; nothing yet says whether `M` is a method or a function.

## Resolve

- Links each name to its declaration and assigns types.
- Fills extra fields on the same nodes:

| Field | Meaning |
|---|---|
| `Expression.Resolved` | the expression after desugaring |
| `BinaryExpr.ResolvedOp` | the typed operator: int `Add` vs sequence `Concat` |
| `AssignStatement.ResolvedStatements` | plain assignments, or a `CallStmt` for a method call |

- Rejects compiled code that reads a ghost value.

## Verify

- Skipped here (`--no-verify`); `proofs.py` verifies the proofs.

## Compile

- `dafny translate py` writes Python. Ghost code is erased.

## Ghost

- Ghost is a flag on a declaration: a parameter, a local, a function.
- `deghost` clears flags before resolution, so the resolver checks its work.
- A variable `deghost` misses gives a resolver error, not a wrong program.
