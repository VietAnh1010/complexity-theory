// DafnySteps CLI.
//   DafnySteps deghost IN.dfy OUT.dfy [trace] [contracts] [counter=steps] [points=P.json]
// prints the deghosted program (included files inlined) so it can be read and
// tested; the plugin (Plugin.cs) applies the same pass inside `dafny`.
//   DafnySteps annotate IN.dfy OUT.dfy [counter=steps] [enable=functions,seq,arrays]
// prints IN with a ghost step counter added (Annotate.cs). Code the cost model
// does not cover is an error, unless `enable=` names a rule for it (CostRules.cs).
using System.Text.Json;
using Microsoft.Dafny;

namespace DafnySteps;

public static class Cli {
  public static Deghost DeghostFromArgs(IEnumerable<string> args, out string pointsPath) {
    var pass = new Deghost();
    pointsPath = null;
    foreach (var a in args) {
      var (key, value) = a.Split('=', 2) is [var k, var v] ? (k, v) : (a, null);
      switch (key) {
        case "trace": pass.Trace = true; break;
        case "contracts": pass.Contracts = true; break;
        case "counter": pass.Counter = value; break;
        case "points": pointsPath = value; break;
        default: throw new ArgumentException($"unknown argument {a}");
      }
    }
    return pass;
  }

  public static async Task<int> Main(string[] args) {
    if (args is ["annotate", var src, var dst, .. var options]) {
      var annotate = new Annotate();
      foreach (var option in options) {
        switch (option.Split('=', 2)) {
          case ["counter", var name]:
            annotate.Counter = name;
            break;
          case ["enable", var names]:
            annotate.Enabled.UnionWith(names.Split(','));
            break;
          default:
            throw new ArgumentException($"unknown argument {option}");
        }
      }
      if (annotate.Enabled.Except(Annotate.Rules.Keys).FirstOrDefault() is { } unknown) {
        throw new ArgumentException($"unknown rule {unknown}; rules: {string.Join(", ", Annotate.Rules.Keys)}");
      }
      return await RunAnnotate(src, dst, annotate);
    }
    if (args is not ["deghost", var input, var output, ..]) {
      Console.Error.WriteLine("usage: DafnySteps deghost IN.dfy OUT.dfy [trace] [contracts] [counter=steps] [points=P.json]\n"
                              + "       DafnySteps annotate IN.dfy OUT.dfy [counter=steps] [enable=functions,seq,arrays]");
      return 2;
    }
    var program = await Ast.Load(input, resolve: false);
    if (program == null) {
      return 1;
    }
    var pass = DeghostFromArgs(args.Skip(3), out var pointsPath);
    pass.Apply(program.DefaultModuleDef);
    await using (var wr = new StreamWriter(output)) {
      Ast.Print(program, wr);
    }
    if (pointsPath != null) {
      File.WriteAllText(pointsPath, JsonSerializer.Serialize(pass.Points));
    }
    return 0;
  }

  static async Task<int> RunAnnotate(string input, string output, Annotate pass) {
    var resolved = await Ast.Load(input, resolve: true);
    var parsed = resolved == null ? null : await Ast.Load(input, resolve: false);
    if (parsed == null) {
      return 1;
    }
    var file = new Uri(Path.GetFullPath(input));
    try {
      pass.Apply(resolved, parsed, file);
    } catch (InvalidOperationException e) {
      Console.Error.WriteLine($"{input}: {e.Message}");
      return 1;
    }
    var dir = Path.GetDirectoryName(Path.GetFullPath(output))!;
    await using (var wr = new StreamWriter(output)) {
      foreach (var inc in parsed.Compilation.Includes.Where(i => i.IncluderFilename == file)) {
        wr.WriteLine($"include \"{Path.GetRelativePath(dir, inc.IncludedFilename.LocalPath)}\"");
      }
      // Print only the input file's declarations; its includes stay includes.
      // PrintTopLevelDecls, not Ast.Print: no `// dafny` header after the includes.
      parsed.DefaultModuleDef.SourceDecls.RemoveAll(d => d.Origin.Uri != file);
      wr.WriteLine();
      new Printer(wr, parsed.Options, PrintModes.Everything)
        .PrintTopLevelDecls(parsed.Compilation, parsed.DefaultModuleDef.TopLevelDecls, 0, null);
    }
    return 0;
  }
}
