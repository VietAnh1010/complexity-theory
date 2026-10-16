# 3. The pipeline inside `dafny`

```
parse → [plugin PreResolve] → resolve + type-check → verify (Boogie → Z3) → compile
```

## Parse

- The output is a syntax tree. Names are unresolved strings.
- A name is a `NameSegment`; `M.x` is an `ExprDotName`.
- `x := M(a)` is an `AssignStatement` whose right side is an `ApplySuffix`.
- At this stage nothing says whether `M` is a method or a function.
- Children: `INode.PreResolveChildren`. `Ast.Descendants` walks these.

## Resolve

- Links each name to its declaration and assigns types.
- Resolution fills extra fields on the same nodes:

| Field | Meaning |
|---|---|
| `Expression.Resolved` | the expression after desugaring, e.g. `IdentifierExpr`, `FunctionCallExpr` |
| `BinaryExpr.ResolvedOp` | the typed operator: int `Add` vs sequence `Concat` |
| `AssignStatement.ResolvedStatements` | `SingleAssignStmt`s, or a `CallStmt` for a method call |
| `CallStmt.Method`, `FunctionCallExpr.Function` | the called declaration |

- Children: `INode.Children`.
- The resolver also enforces ghost rules (below).

## Verify

- Dafny translates to Boogie, which sends verification conditions to Z3.
- The tools here skip it with `--no-verify`; `proofs.py` verifies proofs.

## Compile

- `dafny translate py` writes Python; `--include-runtime` adds the `_dafny` package.
- Ghost code is erased here: ghost variables, lemmas, `assert`, invariants, contracts.

## Ghost versus compiled

- Ghost is a flag on a declaration:
  - `Formal.IsGhost` (a parameter),
  - `LocalVariable.IsGhost`,
  - `MemberDecl.IsGhost` (a function or method).
- The resolver rejects compiled code that reads a ghost value.
- Deghost clears flags before resolution, so the resolver checks its work.
- A variable the pass misses yields a resolver error, not a wrong program.
- `MemberDecl.IsGhost` has no setter; `Deghost.MakeCompiled` sets the private field `isGhost` by reflection.
