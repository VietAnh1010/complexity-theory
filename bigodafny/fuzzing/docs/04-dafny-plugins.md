# 4. Plugins, source ranges, the printer

## Plugins

- `dafny ... --plugin "DafnySteps.dll,trace contracts"` loads a plugin.
- Dafny splits the text after the comma on spaces and passes the words to the plugin.
- Dafny calls the plugin's `PreResolve` before resolution. `Plugin.cs` runs `deghost` there.
- The plugin takes the same arguments as the `deghost` CLI (06).
- The Dafny Reference Manual describes plugins in "Plugins to Dafny" and marks them experimental.

## Source ranges

- Every node stores the position of its source text (`Origin`).
- `annotate` loads a file twice. Two nodes with the same position are the same code.

## The printer

- `Printer` writes a syntax tree back out as Dafny source.
- Print a parsed tree. A resolved tree prints Dafny's rewrites too.
- Comments are not printed.

## The prelude

- Every row starts with `include "../../prelude.dfy"`.
- `deghost` copies the whole prelude into its output; `annotate` keeps the `include` line.
