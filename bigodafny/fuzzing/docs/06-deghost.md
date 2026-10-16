# 6. Deghost (`Deghost.cs`)

Makes a ghost step counter compiled. Runs on the parse tree, before
resolution. The CLI (`Program.cs`) and the plugin (`Plugin.cs`) run the same
pass. Sample output: `demo/2286_319.deghost.dfy`.

## Analysis: what becomes compiled

Variables are matched by name within their method; there are no resolved
variables yet.

1. Seed: each compiled method's out-parameter named `steps`.
2. Repeat over every assignment in every method until nothing new is marked:
   - assignment to a compiled variable → the right side's variables become compiled;
   - the `if` and `while` guards around that assignment → compiled;
   - `x, s := M(..)` with `s` compiled → `M`'s out-parameter at `s`'s position is compiled;
   - an argument for a compiled in-parameter → its variables become compiled;
   - a ghost function named in any of these → compiled, with the functions it calls.
3. With `contracts`, ghost functions in `Solve`'s `requires` and `ensures` are also compiled.

Code: `FindCompiledCode`, `AnalysisRound`, `VisitAssignment`, `MarkFlowInto`.

## Rewriting

- `MakeCompiled` clears the ghost flag on every marked formal, local and function.
- Ghost statements (`assert`, lemma calls, invariants) stay; compilation erases them.

## Trace points (`trace`)

- After each assignment to `steps`: `print <id>, steps;`, kind `update`.
- First in each loop body: `print <id>, steps;`, kind `loop`.
- `Points` lists id, method, line, column and kind.
- Line and column refer to the input `.dfy`, not the printed output.
- Ids are numbered in insertion order, not source order.

## Contract checks (`contracts`)

- Adds `TraceRequires(ins) returns (ok)`: whether `Solve`'s `requires` hold.
- Adds `TraceBound(ins, outs) returns (ok)`: whether `Solve`'s `ensures` hold.
- `TraceBound` takes only compiled outs and skips an `ensures` that names a ghost out.
- Each clause becomes one nested `if`, not a `&&` chain.
- Reason: the printer drops parentheses, so a printed `&&` chain could group differently.
- With no `ensures`, `TraceBound` always returns true.

## Example (`2286_319`)

Proof copy:

```dafny
method Fac2286(x: int) returns (p: int, ghost steps: nat)
  ...
  steps := 1;
  while i <= x ... {
    p := p * i;
    i := i + 1;
    steps := steps + 4;
  }
```

After `deghost ... trace contracts`:

```dafny
method Fac2286(x: int) returns (p: int, steps: nat)
  ...
  steps := 1;
  print 2, steps;
  while i <= x ... {
    print 3, steps;
    p := p * i;
    i := i + 1;
    steps := steps + 4;
    print 4, steps;
  }
```
