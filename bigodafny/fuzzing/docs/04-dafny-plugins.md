# 4. Plugins, source ranges, the printer

## The plugin API

- The Dafny Reference Manual documents it under "Plugins to Dafny" and calls it experimental.
- Command line: `dafny ... --plugin "path/DafnySteps.dll,arg1 arg2"`.
- Dafny splits the text after the first comma on spaces and passes it to `ParseArguments`.
- Dafny instantiates the DLL's `PluginConfiguration` subclass, `DeghostConfiguration`.
- `GetRewriters` returns one `DeghostRewriter`.
- `Rewriter.PreResolve(module)` runs once per module, in dependency order, before resolution.
- `DeghostRewriter` runs the pass over the whole program on the first call.
- It records the root module in a `ConditionalWeakTable`, so later calls do nothing.
- Dafny may create several rewriters for one program; the table is static for that reason.

Plugin arguments (`Cli.DeghostFromArgs`):

| Argument | Effect |
|---|---|
| `trace` | insert trace points |
| `contracts` | add `TraceRequires` and `TraceBound` |
| `counter=NAME` | the counter's name; default `steps` |
| `points=PATH` | write the trace points as JSON |

## Loading a program outside `dafny`

- `Ast.Load(file, resolve)` builds `DafnyOptions`, reads the file and its includes.
- `resolve: false` calls `DafnyMain.Parse`; `resolve: true` calls `DafnyMain.ParseCheck`.
- It returns null on a parse or resolution error.
- Known bug: a missing input file is reported but the call still returns a program.

## Source ranges

- Every node has an `Origin`: the tokens it spans.
- `Ast.Range(n)` gives (start, end) character offsets in the file.
- `annotate` loads the file twice; equal ranges identify the same node in both trees.
- `Ast.Line(n)` gives the line used in notes and trace points.

## The printer

- `Printer` turns a tree back into Dafny source (`Ast.Print`).
- Print a parsed tree; a resolved tree prints resolver output (triggers, desugarings).
- Comments are lost, including a row's header with its Python source.
- The printer drops parentheses it considers redundant; `Deghost.CheckMethod` works around this.
- The output starts with `// dafny 4.11.0.0` and `// Command Line Options:` lines.

## The prelude

- Rows contain `include "../../prelude.dfy"` and `import opened Prelude`.
- `deghost` prints included files inline, so its output contains the whole prelude.
- `annotate` prints only the input file's declarations and keeps the `include`.
- `CostModel.OfCallee` identifies prelude functions by their module name, `Prelude`.
