// annotate: add a ghost step counter to a plain row, charged per COMPLEXITY.md.
//
// The program is loaded twice from the same file. The resolved copy says what
// each node is (a `+` on sequences or on ints, a method call or a function
// call); the parse-only copy is changed and printed, because printing a
// resolved program leaks resolver output (triggers, desugarings). A node is
// found in the other copy by its source range.
//
// Each compiled method of the input file gains:
// - an out-parameter `ghost steps: nat`, and `steps := 0;` first;
// - `steps := steps + <cost>;` before each statement whose own expressions
//   cost something (CostModel.cs);
// - in each loop body, first, the iteration and its guard; after the loop,
//   the guard's last, failing evaluation;
// - for a call `x := M(..)` to an annotated method, a ghost lhs `s<k>` that
//   receives M's steps, added to `steps` after the call.
//
// The output resolves but does not verify: invariants and the bound are the
// proof's work. A charge the model does not cover is recorded in Notes.
using Microsoft.Dafny;
using DafnyProgram = Microsoft.Dafny.Program;

namespace DafnySteps;

public class Annotate {
  public string Counter = "steps";
  public readonly List<string> Notes = [];

  readonly Dictionary<(int, int), INode> resolvedByRange = new();
  readonly Dictionary<(int, int), INode> parsedByRange = new();
  readonly HashSet<string> annotatedMethods = [];
  /// Statements this pass inserted; they are not charged themselves.
  readonly HashSet<Statement> inserted = [];
  CostModel costs;
  int callTemps;

  public void Apply(DafnyProgram resolvedProgram, DafnyProgram parsedProgram, Uri file) {
    var resolvedMethods = MethodsOf(resolvedProgram, file);
    var parsedMethods = MethodsOf(parsedProgram, file);
    IndexByRange(resolvedByRange, resolvedMethods);
    IndexByRange(parsedByRange, parsedMethods);
    costs = new CostModel(parsedByRange, Notes);

    foreach (var method in parsedMethods) {
      if (Declares(method, Counter)) {
        throw new InvalidOperationException($"{method.Name} already declares {Counter}; pick another counter name");
      }
      annotatedMethods.Add(method.Name);
    }
    foreach (var method in parsedMethods) {
      AddCounter(method);
    }
  }

  void AddCounter(Method method) {
    var o = method.Origin;
    method.Outs.Add(new Formal(o, Counter, new UserDefinedType(o, "nat", null), false, true, null, null));
    var blocks = Ast.Descendants(method.Body).OfType<BlockStmt>().Prepend(method.Body).ToList();
    foreach (var block in blocks) {
      ChargeBlock(block);
    }
    method.Body.Body.Insert(0, Ast.Assign(o, Counter, new LiteralExpr(o, 0)));
  }

  void ChargeBlock(BlockStmt block) {
    var body = new List<Statement>();
    foreach (var s in block.Body) {
      if (inserted.Contains(s)) {
        body.Add(s);
      } else if (resolvedByRange.GetValueOrDefault(Ast.Range(s)) is Statement resolved) {
        ChargeStatement(s, resolved, body);
      } else {
        Notes.Add($"line {Ast.Line(s)}: no resolved statement for {s.GetType().Name}; not charged");
        body.Add(s);
      }
    }
    block.Body.Clear();
    block.Body.AddRange(body);
  }

  /// Append `s` to `body`, with its charges around it.
  void ChargeStatement(Statement s, Statement resolved, List<Statement> body) {
    var o = s.Origin;
    var own = OwnCost(resolved);
    if (!own.IsZero) {
      body.Add(AddToCounter(o, own.ToExpr(o)));
    }
    if (s is ReturnStmt { Rhss: { } returned }) {
      returned.Add(new ExprRhs(new NameSegment(o, Counter, null)));
    }
    body.Add(s);

    if (CalleeOf(resolved) is { } callee && annotatedMethods.Contains(callee)) {
      AddCalleeSteps(s, callee, body);
    }
    if (resolved is WhileStmt loop && s is WhileStmt { Body: { } loopBody }) {
      var guard = costs.Of(loop.Guard);
      var iteration = new Cost { Const = 1 };
      iteration.Add(guard);
      loopBody.Body.Insert(0, AddToCounter(o, iteration.ToExpr(o)));
      if (!guard.IsZero) {
        body.Add(AddToCounter(o, guard.ToExpr(o)));
      }
    } else if (s is ForLoopStmt { Body: { } forBody }) {
      forBody.Body.Insert(0, AddToCounter(o, new LiteralExpr(o, 1)));
    }
  }

  /// `x := M(..)` becomes `x, s<k> := M(..); steps := steps + s<k>;`.
  void AddCalleeSteps(Statement call, string callee, List<Statement> body) {
    var o = call.Origin;
    var temp = $"s{callTemps++}";
    switch (call) {
      case VarDeclStmt { Assign: AssignStatement assign } decl:
        // A ghost out-parameter makes the new local ghost.
        decl.Locals.Add(new LocalVariable(o, temp, null, false));
        assign.Lhss.Add(new AutoGhostIdentifierExpr(o, temp));
        break;
      case AssignStatement assign:
        var declaration = new VarDeclStmt(o, [new LocalVariable(o, temp, new UserDefinedType(o, "nat", null), true)], null);
        body.Insert(body.Count - 1, declaration);
        inserted.Add(declaration);
        assign.Lhss.Add(new NameSegment(o, temp, null));
        break;
      default:
        Notes.Add($"line {Ast.Line(call)}: call to {callee} in a {call.GetType().Name}; its steps are not added");
        return;
    }
    body.Add(AddToCounter(o, new NameSegment(o, temp, null)));
  }

  /// `steps := steps + e;`, marked as inserted.
  Statement AddToCounter(IOrigin o, Expression e) {
    var sum = new BinaryExpr(o, BinaryExpr.Opcode.Add, new NameSegment(o, Counter, null), e);
    var s = Ast.Assign(o, Counter, sum);
    inserted.Add(s);
    return s;
  }

  /// What a statement's own expressions cost, its nested statements excluded.
  Cost OwnCost(Statement s) {
    var c = new Cost();
    if (s.IsGhost) {
      return c;
    }
    switch (s) {
      case VarDeclStmt { Assign: AssignStatement assign }:
        return OwnCost(assign);
      case VarDeclStmt:
      case WhileStmt or BlockStmt or BreakOrContinueStmt:
        return c;   // a loop's guard is charged per iteration, in the body
      case AssignStatement assign:
        foreach (var r in assign.ResolvedStatements ?? []) {
          if (r is SingleAssignStmt single) {
            if (single.Lhs.Resolved is not IdentifierExpr) {
              c.Add(costs.Of(single.Lhs));   // an indexed lhs, `a[i] := ..`
            }
            if (single.Rhs is ExprRhs rhs) {
              c.Add(costs.Of(rhs.Expr));
            } else if (single.Rhs is not HavocRhs) {
              Notes.Add($"line {Ast.Line(s)}: {single.Rhs.GetType().Name} not charged");
            }
          } else if (r is CallStmt call) {
            AddAll(c, call.Args);
          }
        }
        return c;
      case IfStmt i:
        return costs.Of(i.Guard);
      case ForLoopStmt f:
        AddAll(c, [f.Start, f.End]);
        return c;
      case ReturnStmt r:
        AddAll(c, (r.Rhss ?? []).OfType<ExprRhs>().Select(rhs => rhs.Expr));
        return c;
      case PrintStmt p:
        AddAll(c, p.Args);
        return c;
      default:
        Notes.Add($"line {Ast.Line(s)}: {s.GetType().Name} not charged");
        return c;
    }
  }

  void AddAll(Cost c, IEnumerable<Expression> es) {
    foreach (var e in es) {
      c.Add(costs.Of(e));
    }
  }

  /// The method a resolved statement calls, if it is a call.
  static string CalleeOf(Statement s) {
    var assign = s switch {
      VarDeclStmt { Assign: AssignStatement a } => a,
      AssignStatement a => a,
      _ => null,
    };
    return assign?.ResolvedStatements?.OfType<CallStmt>().FirstOrDefault()?.Method.Name;
  }

  static bool Declares(Method method, string name) =>
    method.Ins.Concat(method.Outs).Any(f => f.Name == name)
    || Ast.Descendants(method.Body).OfType<VarDeclStmt>().SelectMany(d => d.Locals).Any(v => v.Name == name);

  static List<Method> MethodsOf(DafnyProgram program, Uri file) =>
    Ast.Members(program.DefaultModuleDef).OfType<Method>()
      .Where(m => m is not Lemma && !m.IsGhost && m.Body != null && m.Origin.Uri == file).ToList();

  static void IndexByRange(Dictionary<(int, int), INode> index, IEnumerable<INode> roots) {
    foreach (var root in roots) {
      // Ancestors come first, so a range keeps its outermost node.
      foreach (var node in Ast.Descendants(root).Prepend(root)) {
        index.TryAdd(Ast.Range(node), node);
      }
    }
  }
}
