// Golden tests. Each cases/<pass>/<name>.dfy runs through the CLI, from its own
// directory. What it writes is compared with the expected files beside it:
//   <name>.expected.dfy   the output; absent when the pass must fail (exit 1)
//   <name>.stderr.txt     notes and errors; absent when stderr is empty
//   <name>.points.json    deghost's trace points
// The output must also resolve. A failing case leaves <name>.actual.* behind
// for diffing. `UPDATE_GOLDEN=1 dotnet test` rewrites the expected files.
using System.Runtime.CompilerServices;
using DafnySteps;

// Tests change Console.Error and the current directory.
[assembly: CollectionBehavior(DisableTestParallelization = true)]

public class GoldenTests {
  static readonly string Cases = Path.Combine(Here(), "cases");
  static readonly bool Update = Environment.GetEnvironmentVariable("UPDATE_GOLDEN") == "1";

  static string Here([CallerFilePath] string path = "") => Path.GetDirectoryName(path);

  public static TheoryData<string> DeghostCases => Names("deghost");
  public static TheoryData<string> AnnotateCases => Names("annotate");

  static TheoryData<string> Names(string pass) =>
    new(Directory.GetFiles(Path.Combine(Cases, pass), "*.dfy")
      .Select(Path.GetFileName).Where(f => f.Split('.').Length == 2)
      .Select(Path.GetFileNameWithoutExtension).Order());

  [Theory, MemberData(nameof(DeghostCases))]
  public Task Deghost(string name) =>
    Check("deghost", name, "trace", "contracts", $"points={name}.actual.points.json");

  [Theory, MemberData(nameof(AnnotateCases))]
  public Task Annotate(string name) => Check("annotate", name);

  [Theory, InlineData("deghost"), InlineData("annotate")]
  public async Task MissingInputFails(string pass) {
    var dir = Directory.CreateTempSubdirectory().FullName;
    var output = Path.Combine(dir, "out.dfy");
    var (code, _) = await Run(dir, [pass, "missing.dfy", output]);
    Assert.Equal(1, code);
    Assert.False(File.Exists(output));
    Directory.Delete(dir, true);
  }

  static async Task Check(string pass, string name, params string[] args) {
    var dir = Path.Combine(Cases, pass);
    var (code, stderr) = await Run(dir, [pass, $"{name}.dfy", $"{name}.actual.dfy", .. args]);
    File.WriteAllText(Path.Combine(dir, $"{name}.actual.stderr.txt"), stderr);

    var produced = File.Exists(Path.Combine(dir, $"{name}.actual.dfy"));
    Assert.Equal(produced ? 0 : 1, code);
    if (produced) {
      Assert.True(await Ast.Load(Path.Combine(dir, $"{name}.actual.dfy"), resolve: true) != null,
        $"{name}.actual.dfy does not resolve");
    }
    var suffixes = new[] { ".dfy", ".stderr.txt", ".points.json" };
    if (Update) {
      foreach (var s in suffixes) {
        Promote(dir, name, s);
      }
      return;
    }
    foreach (var s in suffixes) {
      Assert.Equal(Read(dir, $"{name}.expected{s}"), Read(dir, $"{name}.actual{s}"));
    }
    foreach (var s in suffixes) {
      File.Delete(Path.Combine(dir, $"{name}.actual{s}"));
    }
  }

  /// Run the CLI in `dir`. -> (exit code, stderr)
  static async Task<(int, string)> Run(string dir, string[] args) {
    var cwd = Directory.GetCurrentDirectory();
    var err = Console.Error;
    var captured = new StringWriter();
    Directory.SetCurrentDirectory(dir);
    Console.SetError(captured);
    try {
      return (await Cli.Main(args), captured.ToString());
    } finally {
      Console.SetError(err);
      Directory.SetCurrentDirectory(cwd);
    }
  }

  /// A file's text; "" when it does not exist.
  static string Read(string dir, string file) {
    var path = Path.Combine(dir, file);
    return File.Exists(path) ? File.ReadAllText(path) : "";
  }

  /// Make the actual file the expected one; an empty or missing one removes it.
  static void Promote(string dir, string name, string suffix) {
    var actual = Path.Combine(dir, $"{name}.actual{suffix}");
    var expected = Path.Combine(dir, $"{name}.expected{suffix}");
    if (File.Exists(actual) && new FileInfo(actual).Length > 0) {
      File.Move(actual, expected, overwrite: true);
    } else {
      File.Delete(actual);
      File.Delete(expected);
    }
  }
}
