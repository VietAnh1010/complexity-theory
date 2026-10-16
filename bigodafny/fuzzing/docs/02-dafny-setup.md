# 2. Dafny setup

## Installation

- `dafny` is a .NET program, installed as a dotnet global tool: `~/.dotnet/tools/dafny`.
- The version is pinned in `bigodafny/README.md` § Toolchain.
- Its DLLs are in `~/.dotnet/tools/.store/dafny/4.11.0/dafny/4.11.0/tools/net8.0/any/`.
- `DafnyCore.dll` holds the AST, parser, resolver, printer and compilers.
- `Boogie.*.dll` is the verifier backend; Z3 is a separate binary on `PATH`.

## How DafnySteps links against Dafny

- `DafnySteps.csproj` sets `DafnyDir` to the directory above.
- It references every DLL there except `Dafny.dll`.
- So the tool is compiled against the exact AST that `dafny` uses at run time.
- DafnyCore's API is not stable; it changes between Dafny versions.
- A Dafny upgrade means changing `DafnyDir` and fixing every API call that changed.

## .NET versions

- Dafny targets `net8.0` with `rollForward: Major` (`DafnyDriver.runtimeconfig.json`).
- This machine has only the .NET 10 runtime, so `dafny` runs on .NET 10.
- `DafnySteps` targets `net10.0` so that it loads into that process as a plugin.
- `MSB3277` (assembly version conflicts) is suppressed in the `.csproj`.

## Build

```bash
dotnet build -c Release bigodafny/fuzzing/DafnySteps
# -> DafnySteps/bin/Release/net10.0/DafnySteps.dll  (plugin)
# -> DafnySteps/bin/Release/net10.0/DafnySteps      (CLI)
```

- `bin/` and `obj/` are git-ignored build output.
