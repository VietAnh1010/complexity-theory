// deghost: make a ghost step counter compiled, so it runs.
//
// The pass runs on the parse tree, before resolution, so the CLI (parse,
// transform, print) and the plugin (transform, then Dafny resolves and
// compiles) share it. If the pass leaves a ghost value flowing into compiled
// code, the resolver reports an error; the pass never hides one.
//
// What becomes compiled:
// - each out-parameter named <Counter> of a compiled method;
// - each variable whose value flows into something compiled: the right-hand
//   side of an assignment to it, the guards around that assignment, and the
//   argument passed for a compiled in-parameter;
// - for a call `x, s := M(..)` where `s` is compiled, M's out-parameter in
//   the same position;
// - each ghost function called by such a flow, and the ghost functions it calls.
//
// Variables are matched by name within their method: the pass runs before
// resolution, so there are no resolved variables yet.
using System.Reflection;
using Microsoft.Dafny;

namespace DafnySteps;

/// A trace point: `print Id, steps;` inserted at Line:Col of Method.
public record Point(int Id, string Method, int Line, int Col, string Kind);

public class Deghost {
  public string Counter = "steps";
  /// Insert a trace point after each counter update and at each loop head.
  public bool Trace;
  /// Add TraceRequires and TraceBound, Solve's contract as compiled methods.
  public bool Contracts;
  public readonly List<Point> Points = [];

  Dictionary<string, List<Method>> methodsByName;
  Dictionary<string, List<Function>> functionsByName;
  readonly Dictionary<Method, HashSet<string>> variablesOf = [];
  readonly HashSet<(Method Method, string Variable)> compiledVariables = [];
  readonly HashSet<Function> compiledFunctions = [];

  public void Apply(ModuleDefinition root) {
    var members = Ast.Members(root).ToList();
    var methods = members.OfType<Method>()
      .Where(m => m is not Lemma && !m.IsGhost && m.Body != null).ToList();
    var solve = methods.FirstOrDefault(m => m.Name == "Solve");
    methodsByName = methods.GroupBy(m => m.Name).ToDictionary(g => g.Key, g => g.ToList());
    functionsByName = members.OfType<Function>().GroupBy(f => f.Name).ToDictionary(g => g.Key, g => g.ToList());
    foreach (var method in methods) {
      variablesOf[method] = VariableNames(method);
    }

    FindCompiledCode(methods, Contracts ? solve : null);
    MakeCompiled();
    if (Trace) {
      foreach (var method in methods.Where(HasCounter)) {
        InsertTracePoints(method);
      }
    }
    if (Contracts && solve != null) {
      AddContractChecks(solve);
    }
  }

  // ---- Analysis: what must become compiled --------------------------------

  void FindCompiledCode(List<Method> methods, Method contractsOf) {
    foreach (var method in methods.Where(m => m.Outs.Any(o => o.Name == Counter))) {
      compiledVariables.Add((method, Counter));
    }
    if (contractsOf != null) {
      foreach (var clause in contractsOf.Req.Concat(contractsOf.Ens)) {
        MarkCalledFunctions(clause.E);
      }
    }
    while (AnalysisRound(methods)) { }
  }

  /// One pass over every method; true if it marked anything new.
  bool AnalysisRound(List<Method> methods) {
    var before = compiledVariables.Count + compiledFunctions.Count;
    foreach (var method in methods) {
      foreach (var (assignment, guards) in Assignments(method.Body, [])) {
        VisitAssignment(method, assignment, guards);
      }
    }
    foreach (var function in compiledFunctions.ToList()) {
      MarkCalledFunctions(function.Body);
    }
    return compiledVariables.Count + compiledFunctions.Count > before;
  }

  void VisitAssignment(Method method, AssignStatement assignment, List<Expression> guards) {
    var call = MethodCall(assignment);
    var callees = call == null ? [] : methodsByName[Ast.CalleeName(call)];

    for (var i = 0; i < assignment.Lhss.Count; i++) {
      if (!compiledVariables.Contains((method, LhsName(assignment.Lhss[i])))) {
        continue;
      }
      if (call != null) {
        // `x, s := M(..)`: M's out-parameter at s's position is compiled too.
        foreach (var callee in callees.Where(c => i < c.Outs.Count)) {
          compiledVariables.Add((callee, callee.Outs[i].Name));
        }
      } else if (i < assignment.Rhss.Count && assignment.Rhss[i] is ExprRhs rhs) {
        MarkFlowInto(method, rhs.Expr);
      }
      foreach (var guard in guards) {
        MarkFlowInto(method, guard);
      }
    }

    // An argument passed for a compiled in-parameter is compiled too.
    if (call != null) {
      var args = call.Bindings.ArgumentBindings;
      foreach (var callee in callees) {
        for (var j = 0; j < Math.Min(args.Count, callee.Ins.Count); j++) {
          if (compiledVariables.Contains((callee, callee.Ins[j].Name))) {
            MarkFlowInto(method, args[j].Actual);
          }
        }
      }
    }
  }

  /// Mark the variables of `method` and the functions that `e` mentions.
  void MarkFlowInto(Method method, Expression e) {
    foreach (var name in Ast.NamesIn(e).Where(variablesOf[method].Contains)) {
      compiledVariables.Add((method, name));
    }
    MarkCalledFunctions(e);
  }

  void MarkCalledFunctions(Expression e) {
    foreach (var name in Ast.NamesIn(e)) {
      foreach (var function in functionsByName.GetValueOrDefault(name, []).Where(f => f.IsGhost)) {
        compiledFunctions.Add(function);
      }
    }
  }

  /// The call `M(..)` if the assignment's right-hand side is a method call.
  ApplySuffix MethodCall(AssignStatement assignment) {
    if (assignment.Rhss is [ExprRhs { Expr: ApplySuffix call }]
        && Ast.CalleeName(call) is { } name && methodsByName.ContainsKey(name)) {
      return call;
    }
    return null;
  }

  /// Each assignment below `s`, with the if and while guards around it.
  static IEnumerable<(AssignStatement, List<Expression>)> Assignments(Statement s, List<Expression> guards) {
    if (s == null) {
      yield break;
    }
    if (s is AssignStatement assignment) {
      yield return (assignment, guards);
    }
    var (children, guard) = s switch {
      IfStmt i => (new[] { i.Thn, i.Els }, i.Guard),
      WhileStmt w => (new Statement[] { w.Body }, w.Guard),
      _ => (s.PreResolveSubStatements.ToArray(), null),
    };
    var inner = guard == null ? guards : [.. guards, guard];
    foreach (var child in children) {
      foreach (var found in Assignments(child, inner)) {
        yield return found;
      }
    }
  }

  static HashSet<string> VariableNames(Method method) =>
    method.Ins.Concat(method.Outs).Select(f => f.Name)
      .Concat(Locals(method).Select(v => v.Name)).ToHashSet();

  static IEnumerable<LocalVariable> Locals(Method method) =>
    Ast.Descendants(method.Body).OfType<VarDeclStmt>().SelectMany(d => d.Locals);

  static string LhsName(Expression lhs) => lhs switch {
    NameSegment s => s.Name,
    IdentifierExpr i => i.Name,
    _ => null,
  };

  // ---- Rewriting -------------------------------------------------------

  void MakeCompiled() {
    foreach (var (method, name) in compiledVariables) {
      foreach (var formal in method.Ins.Concat(method.Outs).Where(f => f.Name == name)) {
        formal.IsGhost = false;
      }
      foreach (var local in Locals(method).Where(v => v.Name == name)) {
        local.IsGhost = false;
      }
    }
    // MemberDecl.IsGhost has no setter; set its protected backing field.
    var isGhost = typeof(MemberDecl).GetField("isGhost", BindingFlags.NonPublic | BindingFlags.Instance)!;
    foreach (var function in compiledFunctions) {
      isGhost.SetValue(function, false);
    }
  }

  bool HasCounter(Method method) => method.Outs.Any(o => o.Name == Counter);

  void InsertTracePoints(Method method) {
    var blocks = Ast.Descendants(method.Body).OfType<BlockStmt>().Prepend(method.Body).ToList();
    foreach (var block in blocks) {
      var body = new List<Statement>();
      foreach (var s in block.Body) {
        body.Add(s);
        if (s is OneBodyLoopStmt { Body: { } loopBody }) {
          loopBody.Body.Insert(0, TracePoint(method, s, "loop"));
        }
        if (AssignsCounter(s)) {
          body.Add(TracePoint(method, s, "update"));
        }
      }
      block.Body.Clear();
      block.Body.AddRange(body);
    }
  }

  bool AssignsCounter(Statement s) => s switch {
    AssignStatement a => a.Lhss.Any(lhs => LhsName(lhs) == Counter),
    VarDeclStmt d => d.Locals.Any(v => v.Name == Counter),
    _ => false,
  };

  /// `print <id>, steps;`, recorded in Points.
  PrintStmt TracePoint(Method method, Statement at, string kind) {
    var id = Points.Count;
    var where = at.Origin.Center;
    Points.Add(new Point(id, method.Name, where.line, where.col, kind));
    var o = at.Origin;
    return new PrintStmt(o, [new LiteralExpr(o, id), new NameSegment(o, Counter, null)]);
  }

  // ---- Contract checks -------------------------------------------------

  /// Add `TraceRequires(ins)` and `TraceBound(ins, outs)` beside Solve. Each
  /// returns whether Solve's requires (ensures) hold. TraceBound takes only
  /// the compiled outs, and skips an ensures clause that names a ghost out.
  void AddContractChecks(Method solve) {
    var ghostOuts = solve.Outs.Where(f => f.IsGhost).Select(f => f.Name).ToHashSet();
    var ensures = solve.Ens.Where(c => !Ast.NamesIn(c.E).Any(ghostOuts.Contains)).ToList();
    var compiledOuts = solve.Outs.Where(f => !f.IsGhost).ToList();

    var cls = (TopLevelDeclWithMembers)solve.EnclosingClass;
    cls.Members.Add(CheckMethod(solve, "TraceRequires", solve.Ins, solve.Req));
    cls.Members.Add(CheckMethod(solve, "TraceBound", [.. solve.Ins, .. compiledOuts], ensures));
    cls.SetMembersBeforeResolution();
  }

  /// method <name>(<params>) returns (ok: bool) {
  ///   ok := false;
  ///   if c1 { if c2 { .. ok := true; } }
  /// }
  /// Nested ifs, not one `&&` chain: the printer drops the parentheses that
  /// would keep a clause's own `&&` grouped, so the CLI's printed program
  /// would group differently from the plugin's AST.
  static Method CheckMethod(Method solve, string name, List<Formal> parameters, List<AttributedExpression> clauses) {
    var cloner = new Cloner();
    var o = solve.Origin;
    var ins = parameters.Select(f =>
      new Formal(f.Origin, f.Name, cloner.CloneType(f.SyntacticType), true, false, null, null)).ToList();
    var ok = new Formal(o, "ok", Microsoft.Dafny.Type.Bool, false, false, null, null);

    Statement check = Ast.Assign(o, "ok", new LiteralExpr(o, true));
    foreach (var clause in Enumerable.Reverse(clauses)) {
      check = new IfStmt(o, false, cloner.CloneExpr(clause.E), new BlockStmt(o, [check]), null);
    }
    var body = new BlockStmt(o, [Ast.Assign(o, "ok", new LiteralExpr(o, false)), check]);

    return new Method(o, new Name(o, name), null, false, false, [], ins, [], [],
      new Specification<FrameExpression>([], null), new Specification<Expression>([], null),
      [ok], new Specification<FrameExpression>([], null), body, null);
  }
}
