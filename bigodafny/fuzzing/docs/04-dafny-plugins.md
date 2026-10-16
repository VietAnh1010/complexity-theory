# 4. Plugins and printing

## The plugin API

- `dafny ... --plugin "DafnySteps.dll,trace contracts"` loads the DLL.
- Text after the comma is split on spaces and passed to the plugin as arguments.
- Dafny calls the plugin's `PreResolve` before resolution; `Plugin.cs` runs `deghost` there.
- The arguments are the same as the CLI's (06).
- The Dafny Reference Manual documents the API ("Plugins to Dafny") as experimental.

## Source ranges

- Every node records the source text it came from (`Origin`).
- `annotate` loads a file twice; equal ranges identify the same node in both trees.

## The printer

- `Printer` turns a tree back into Dafny source.
- It prints a parsed tree; a resolved tree would print resolver output too.
- Comments are lost.

## The prelude

- Rows `include "../../prelude.dfy"`.
- `deghost` prints the prelude inline; `annotate` keeps the `include`.
