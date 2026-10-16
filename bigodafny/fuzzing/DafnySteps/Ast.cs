// Loading, walking and printing Dafny programs with DafnyCore, the AST `dafny`
// itself uses. DafnyCore is not a stable API: this is built against the
// Dafny the toolchain pins (4.11.0).
using Microsoft.Dafny;
using DafnyProgram = Microsoft.Dafny.Program;

namespace DafnySteps;

public static class Ast {
  public static DafnyOptions Options() =>
    DafnyOptions.CreateUsingOldParser(Console.Error, TextReader.Null);

  /// Parse `file` and the files it includes. With `resolve`, also resolve and
  /// type-check. Null on error; the errors are on stderr.
  public static async Task<DafnyProgram> Load(string file, bool resolve) {
    var options = Options();
    var reporter = new ConsoleErrorReporter(options);
    var files = new List<DafnyFile>();
    await foreach (var df in DafnyFile.CreateAndValidate(OnDiskFileSystem.Instance, reporter, options,
                     new Uri(Path.GetFullPath(file)), Token.Cli)) {
      files.Add(df);
    }
    var (program, err) = resolve
      ? await DafnyMain.ParseCheck(TextReader.Null, files, file, options)
      : await DafnyMain.Parse(files, file, options);
    if (err != null) {
      Console.Error.WriteLine(err);
      return null;
    }
    return program;
  }

  /// Print a parsed (unresolved) program as Dafny source, included files inlined.
  public static void Print(DafnyProgram program, TextWriter wr) {
    new Printer(wr, program.Options, PrintModes.Everything).PrintProgramLargeStack(program, false);
  }

  /// Every module definition under `root`, `root` included.
  public static IEnumerable<ModuleDefinition> Modules(ModuleDefinition root) {
    yield return root;
    foreach (var d in root.SourceDecls.OfType<LiteralModuleDecl>()) {
      foreach (var m in Modules(d.ModuleDef)) {
        yield return m;
      }
    }
  }

  public static ModuleDefinition Root(ModuleDefinition m) {
    while (m.EnclosingModule != null) {
      m = m.EnclosingModule;
    }
    return m;
  }

  public static IEnumerable<MemberDecl> Members(ModuleDefinition root) =>
    Modules(root).SelectMany(m => m.TopLevelDecls.OfType<TopLevelDeclWithMembers>())
      .SelectMany(d => d.Members);

  /// All nodes below `n` in the parse tree (before resolution).
  public static IEnumerable<INode> Descendants(INode n) {
    var stack = new Stack<INode>();
    stack.Push(n);
    while (stack.Count > 0) {
      var cur = stack.Pop();
      foreach (var c in cur.PreResolveChildren) {
        if (c != null) {
          yield return c;
          stack.Push(c);
        }
      }
    }
  }

  /// The name an expression calls, for `f(..)` or `M.f(..)`; else null.
  public static string CalleeName(Expression e) =>
    e is ApplySuffix a ? NameOf(a.Lhs) : null;

  /// The name a NameSegment or `M.x` refers to; else null.
  public static string NameOf(Expression e) => e switch {
    NameSegment s => s.Name,
    ExprDotName d => d.SuffixName,
    _ => null,
  };

  /// Every name an expression mentions: variables and called functions alike.
  public static IEnumerable<string> NamesIn(Expression e) {
    if (e == null) {
      yield break;
    }
    foreach (var n in Descendants(e).Prepend(e)) {
      if (n is Expression x && NameOf(x) is { } name) {
        yield return name;
      }
    }
  }

  public static int Line(INode n) => n.Origin.Center.line;

  /// A node's source range, as (start, end) token positions.
  public static (int, int) Range(INode n) {
    var r = n.Origin.EntireRangeWithFallback;
    return (r.StartToken.pos, r.EndToken.pos);
  }

  /// `name := rhs;`
  public static AssignStatement Assign(IOrigin o, string name, Expression rhs) =>
    new(o, [new NameSegment(o, name, null)], [new ExprRhs(rhs)]);
}
