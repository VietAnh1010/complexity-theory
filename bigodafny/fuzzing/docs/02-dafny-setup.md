# 2. Dafny setup

- `dafny` is a .NET program, installed as a dotnet tool at `~/.dotnet/tools/dafny`.
- Its version is fixed in `bigodafny/README.md` § Toolchain.
- Its DLLs are in `~/.dotnet/tools/.store/dafny/4.11.0/dafny/4.11.0/tools/net8.0/any/`.
- `DafnyCore.dll` contains the AST, parser, resolver, printer and compilers.

## How DafnySteps uses Dafny

- `fuzzing/Directory.Build.props` adds those DLLs to both C# projects.
- `DafnySteps` therefore uses the same AST classes as `dafny`.
- These classes change between Dafny versions. To upgrade Dafny, edit that file and fix the errors.
- `dafny` runs on .NET 10 here, so `DafnySteps` targets `net10.0`.

## Build

```bash
dotnet build -c Release DafnySteps     # from fuzzing/
# DafnySteps/bin/Release/net10.0/DafnySteps.dll   the plugin
# DafnySteps/bin/Release/net10.0/DafnySteps       the CLI
```
