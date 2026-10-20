// DafnySteps CLI.
//   DafnySteps deghost IN.dfy OUT.dfy [trace[=LINE,..]] [contracts] [counter=steps] [points=P.json]
// prints the deghosted program (included files inlined) so it can be read and
// tested; the plugin (Plugin.cs) applies the same pass inside `dafny`.
//   DafnySteps annotate IN.dfy OUT.dfy [counter=steps] [enable=functions,seq,arrays]
// prints IN with a ghost step counter added (Annotate.cs), keeping the Python
// block of IN's header and nothing else of it. Code the cost model does not
// cover is an error, unless `enable=` names a rule for it (CostRules.cs).
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
        case "trace":
          pass.Trace = true;
          pass.TraceLines = value?.Split(',').Select(int.Parse).ToHashSet();
          break;
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
      Console.Error.WriteLine("usage: DafnySteps deghost IN.dfy OUT.dfy [trace[=LINE,..]] [contracts] [counter=steps] [points=P.json]\n"
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

  /// The lines from `// --- Python` to the `// ----` line closing it; none if absent.
  static List<string> PythonBlock(List<string> header) {
    var start = header.FindIndex(l => l.StartsWith("// --- Python"));
    var end = start < 0 ? -1 : header.FindIndex(start + 1, l => l.StartsWith("// ----------"));
    return end < 0 ? [] : header[start..(end + 1)];
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
      // The printer drops comments, so the header's Python block is copied
      // as text. The rest of the header (title, label, a label audit's
      // verdict) is left out: the output goes to agents guessing the complexity.
      var header = PythonBlock(File.ReadLines(input)
        .TakeWhile(l => l.StartsWith("//") || l.Trim() == "").ToList());
      var includes = parsed.Compilation.Includes.Where(i => i.IncluderFilename == file).ToList();
      foreach (var line in header) {
        wr.WriteLine(line);
      }
      if (header.Count > 0 && includes.Count > 0) {
        wr.WriteLine();
      }
      foreach (var inc in includes) {
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
