// The deghost pass as a Dafny plugin:
//   dafny translate py --plugin "DafnySteps.dll,trace contracts points=P.json" row.dfy
// Dafny splits the arguments after the first comma on spaces. Arguments:
// `trace` (or `trace=LINE,..`: only those source lines; `trace=loops`: only loop heads), `contracts`,
// `counter=<name>`, `points=<path>` (the trace points, as JSON).
//
// Plugins get PreResolve once per module, in dependency order, so the first
// call comes before any module is resolved. That call runs the pass over the
// whole program from the root module; later calls do nothing. Dafny may create
// several rewriters for one program, so "done" is recorded per root module.
using System.Runtime.CompilerServices;
using System.Text.Json;
using Microsoft.Dafny;
using Microsoft.Dafny.Plugins;

namespace DafnySteps;

public class DeghostConfiguration : PluginConfiguration {
  string[] args = [];

  public override void ParseArguments(string[] args) => this.args = args;

  public override Rewriter[] GetRewriters(ErrorReporter reporter) => [new DeghostRewriter(reporter, args)];
}

public class DeghostRewriter(ErrorReporter reporter, string[] args) : Rewriter(reporter) {
  static readonly ConditionalWeakTable<ModuleDefinition, object> Done = new();

  public override void PreResolve(ModuleDefinition module) {
    var root = Ast.Root(module);
    if (!Done.TryAdd(root, null)) {
      return;
    }
    var pass = Cli.DeghostFromArgs(args, out var pointsPath);
    pass.Apply(root);
    if (pointsPath != null) {
      File.WriteAllText(pointsPath, JsonSerializer.Serialize(pass.Points));
    }
  }
}
