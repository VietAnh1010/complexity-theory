# 2. Dafny setup

- `dafny` is a .NET program, installed as a dotnet global tool: `~/.dotnet/tools/dafny`.
- The version is pinned in `bigodafny/README.md` § Toolchain.
- Its DLLs are in `~/.dotnet/tools/.store/dafny/4.11.0/dafny/4.11.0/tools/net8.0/any/`.
- `DafnyCore.dll` holds the AST, parser, resolver, printer and compilers.

## How DafnySteps uses it

- `fuzzing/Directory.Build.props` points both C# projects at those DLLs.
- So `DafnySteps` uses the same AST classes as `dafny` itself.
- That API is not stable: a Dafny upgrade means editing that file and fixing what broke.
- `dafny` runs on the installed .NET 10, so `DafnySteps` targets `net10.0` too.

## Build

```bash
dotnet build -c Release DafnySteps     # from fuzzing/
# DafnySteps/bin/Release/net10.0/DafnySteps.dll   the plugin
# DafnySteps/bin/Release/net10.0/DafnySteps       the CLI
```
