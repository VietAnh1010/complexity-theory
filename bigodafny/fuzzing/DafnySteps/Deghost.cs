// deghost: make a ghost step counter compiled, so it runs.
//
// Works on the parse tree, before resolution, so the same pass serves the CLI
// (parse, transform, print) and the plugin (transform in PreResolve, then
// Dafny resolves and compiles). The resolver checks the result: if the pass
// leaves a ghost value flowing into compiled code, Dafny reports an error.
//
// What becomes compiled:
// - every out-parameter named <counter> of a compiled method;
// - every variable whose value flows into a compiled counter: a right-hand
//   side assigned to it, a guard enclosing that assignment, a call argument
//   bound to a counter in-parameter;
// - for a call `x, s := M(..)` with `s` a counter, M's out-parameter at s's
//   position (it becomes a counter of M);
// - every ghost function such a flow calls, and the ghost functions those call.
//
// Names are matched before resolution, per method: a variable is identified
// by its name within its method. Shadowing two variables of one name makes
// both compiled; if that is wrong, the resolver rejects the program.
//
// With trace on, a `print <id>, <counter>;` follows each assignment to a
// counter and opens each loop body of a method with a counter. Each id is a
// Point in `Points`.
using System.Reflection;
using Microsoft.Dafny;

namespace DafnySteps;

public record Point(int Id, string Method, int Line, int Col, string Kind);

public class Deghost {
  public string Counter = "steps";
  public bool Trace;
  public bool Contracts;
  public readonly List<Point> Points = [];

  Dictionary<string, List<Method>> methods;
  Dictionary<string, List<Function>> functions;
  readonly HashSet<(Method, string)> counters = [];
  readonly HashSet<Function> compiled = [];

  public void Apply(ModuleDefinition root) {
    var members = Ast.Members(root).ToList();
    var ms = members.OfType<Method>().Where(m => m is not Lemma && !m.IsGhost && m.Body != null).ToList();
    methods = ms.GroupBy(m => m.Name).ToDictionary(g => g.Key, g => g.ToList());
    functions = members.OfType<Function>().GroupBy(f => f.Name).ToDictionary(g => g.Key, g => g.ToList());

    foreach (var m in ms) {
      if (m.Outs.Any(o => o.Name == Counter)) {
        counters.Add((m, Counter));
      }
    }
    var solve = ms.FirstOrDefault(m => m.Name == "Solve");
    if (Contracts && solve != null) {
      foreach (var e in solve.Req.Concat(solve.Ens)) {
        DependFunctions(e.E);
      }
    }
    while (Step(ms)) { }

    foreach (var (m, name) in counters) {
      foreach (var f in m.Ins.Concat(m.Outs).Where(f => f.Name == name)) {
        f.IsGhost = false;
      }
      foreach (var v in Locals(m).Where(v => v.Name == name)) {
        v.IsGhost = false;
      }
    }
    var isGhost = typeof(MemberDecl).GetField("isGhost", BindingFlags.NonPublic | BindingFlags.Instance)!;
    foreach (var f in compiled) {
      isGhost.SetValue(f, false);
    }
    if (Trace) {
      foreach (var m in ms.Where(m => counters.Contains((m, Counter)) && m.Outs.Any(o => o.Name == Counter))) {
        InsertTrace(m);
      }
    }
    if (Contracts && solve != null) {
      AddContractChecks(solve);
    }
  }

  /// One round of the flow analysis; true if anything was added.
  bool Step(List<Method> ms) {
    var before = counters.Count + compiled.Count;
    foreach (var m in ms) {
      var vars = m.Ins.Concat(m.Outs).Select(f => f.Name).Concat(Locals(m).Select(v => v.Name)).ToHashSet();
      Walk(m.Body, [], (s, guards) => {
        if (s is not AssignStatement a) {
          return;
        }
        var call = a.Rhss.Count == 1 && a.Rhss[0] is ExprRhs er && Ast.CalleeName(er.Expr) is { } n
                   && methods.TryGetValue(n, out var callees) ? (er.Expr as ApplySuffix, callees) : (null, null);
        for (var i = 0; i < a.Lhss.Count; i++) {
          var lhs = LhsName(a.Lhss[i]);
          if (lhs == null || !counters.Contains((m, lhs))) {
            continue;
          }
          if (call.Item1 != null) {
            foreach (var c in call.callees.Where(c => i < c.Outs.Count)) {
              counters.Add((c, c.Outs[i].Name));
            }
          } else if (i < a.Rhss.Count && a.Rhss[i] is ExprRhs r) {
            Depend(m, vars, r.Expr);
          }
          foreach (var g in guards) {
            Depend(m, vars, g);
          }
        }
        if (call.Item1 != null) {
          var args = call.Item1.Bindings.ArgumentBindings;
          foreach (var c in call.callees) {
            for (var j = 0; j < Math.Min(args.Count, c.Ins.Count); j++) {
              if (counters.Contains((c, c.Ins[j].Name))) {
                Depend(m, vars, args[j].Actual);
              }
            }
          }
        }
      });
    }
    foreach (var f in compiled.ToList()) {
      DependFunctions(f.Body);
    }
    return counters.Count + compiled.Count > before;
  }

  void Depend(Method m, HashSet<string> vars, Expression e) {
    foreach (var name in Ast.NamesIn(e)) {
      if (vars.Contains(name)) {
        counters.Add((m, name));
      }
    }
    DependFunctions(e);
  }

  void DependFunctions(Expression e) {
    foreach (var name in Ast.NamesIn(e)) {
      if (functions.TryGetValue(name, out var fs)) {
        foreach (var f in fs.Where(f => f.IsGhost)) {
          compiled.Add(f);
        }
      }
    }
  }

  static string LhsName(Expression e) => e switch {
    NameSegment s => s.Name,
    IdentifierExpr i => i.Name,
    _ => null,
  };

  static IEnumerable<LocalVariable> Locals(Method m) =>
    Ast.Descendants(m.Body).OfType<VarDeclStmt>().SelectMany(d => d.Locals);

  /// Visit every statement with the guards of the ifs and loops enclosing it.
  static void Walk(Statement s, List<Expression> guards, Action<Statement, List<Expression>> visit) {
    if (s == null) {
      return;
    }
    visit(s, guards);
    switch (s) {
      case IfStmt i:
        var gi = i.Guard == null ? guards : [.. guards, i.Guard];
        Walk(i.Thn, gi, visit);
        Walk(i.Els, gi, visit);
        break;
      case WhileStmt w:
        Walk(w.Body, w.Guard == null ? guards : [.. guards, w.Guard], visit);
        break;
      default:
        foreach (var c in s.PreResolveSubStatements) {
          Walk(c, guards, visit);
        }
        break;
    }
  }

  void InsertTrace(Method m) {
    var blocks = Ast.Descendants(m.Body).OfType<BlockStmt>().Prepend(m.Body).ToList();
    foreach (var b in blocks) {
      var body = new List<Statement>();
      foreach (var s in b.Body) {
        body.Add(s);
        if (s is OneBodyLoopStmt { Body: { } lb }) {
          lb.Body.Insert(0, TracePoint(m, s, "loop"));
        }
        if (s is AssignStatement a && a.Lhss.Any(l => LhsName(l) == Counter)
            || s is VarDeclStmt d && d.Locals.Any(v => v.Name == Counter)) {
          body.Add(TracePoint(m, s, "update"));
        }
      }
      b.Body.Clear();
      b.Body.AddRange(body);
    }
  }

  PrintStmt TracePoint(Method m, Statement at, string kind) {
    var id = Points.Count;
    var c = at.Origin.Center;
    Points.Add(new Point(id, m.Name, c.line, c.col, kind));
    return new PrintStmt(at.Origin, [new LiteralExpr(at.Origin, id), new NameSegment(at.Origin, Counter, null)]);
  }

  /// `TraceRequires(ins) returns (ok)` and `TraceBound(ins, outs) returns (ok)`:
  /// Solve's requires and ensures as compiled checks, beside Solve. Only
  /// compiled outs are passed; an ensures clause naming a ghost out is skipped.
  void AddContractChecks(Method solve) {
    var cls = (TopLevelDeclWithMembers)solve.EnclosingClass
              ?? throw new InvalidOperationException("Solve has no enclosing class");
    var ghostOuts = solve.Outs.Where(f => f.IsGhost).Select(f => f.Name).ToHashSet();
    var ens = solve.Ens.Where(c => !Ast.NamesIn(c.E).Any(ghostOuts.Contains)).ToList();
    cls.Members.Add(Check(solve, "TraceRequires", solve.Req, []));
    cls.Members.Add(Check(solve, "TraceBound", ens, solve.Outs.Where(f => !f.IsGhost)));
    cls.SetMembersBeforeResolution();
  }

  static Method Check(Method solve, string name, List<AttributedExpression> clauses, IEnumerable<Formal> outs) {
    var cloner = new Cloner();
    var o = solve.Origin;
    var ins = solve.Ins.Concat(outs)
      .Select(f => new Formal(f.Origin, f.Name, cloner.CloneType(f.SyntacticType), true, false, null, null)).ToList();
    // `if c1 { if c2 { .. ok := true; } }`: clauses evaluated in order, each
    // only when the ones before hold. Nested statements, not one `&&` chain,
    // so the printed program groups as the AST does.
    Statement body = new AssignStatement(o, [new NameSegment(o, "ok", null)], [new ExprRhs(new LiteralExpr(o, true))]);
    for (var i = clauses.Count - 1; i >= 0; i--) {
      body = new IfStmt(o, false, cloner.CloneExpr(clauses[i].E), new BlockStmt(o, [body]), null);
    }
    var init = new AssignStatement(o, [new NameSegment(o, "ok", null)], [new ExprRhs(new LiteralExpr(o, false))]);
    return new Method(o, new Name(o, name), null, false, false, [], ins, [], [],
      new Specification<FrameExpression>([], null), new Specification<Expression>([], null),
      [new Formal(o, "ok", Microsoft.Dafny.Type.Bool, false, false, null, null)],
      new Specification<FrameExpression>([], null), new BlockStmt(o, [init, body]), null);
  }
}
