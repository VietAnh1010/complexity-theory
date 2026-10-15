// annotate: add a ghost step counter to a plain row, charged per COMPLEXITY.md.
//
// The program is loaded twice from the same file. The resolved copy says what
// each node is (a `+` on sequences or on ints, a method call or a function
// call); the parse-only copy is changed and printed, because printing a
// resolved program leaks resolver output (triggers, desugarings). Nodes are
// matched by source range: both copies come from one text, so a node's range
// names it in both.
//
// Each compiled method of the input file gains `ghost steps: nat`, `steps := 0`
// first, and `steps := steps + <charge>` before each statement whose own
// expressions cost something. A loop body starts by charging the iteration and
// its guard; the guard's last, failing evaluation is charged after the loop. A
// call `x := M(..)` to an annotated method gains a ghost lhs `s<k>` holding
// M's steps, added after the call.
//
// The output resolves; it does not verify: invariants and the bound are the
// proof's work. A charge the model does not cover is recorded in Notes.
using Microsoft.Dafny;
using DafnyProgram = Microsoft.Dafny.Program;

namespace DafnySteps;

public class Annotate {
  public string Counter = "steps";
  public readonly List<string> Notes = [];

  readonly Dictionary<(int, int), INode> resolved = new();
  readonly Dictionary<(int, int), INode> parsed = new();
  readonly HashSet<string> annotated = [];
  int temps;

  static (int, int) Key(INode n) {
    var r = n.Origin.EntireRangeWithFallback;
    return (r.StartToken.pos, r.EndToken.pos);
  }

  static void Index(Dictionary<(int, int), INode> index, IEnumerable<INode> roots) {
    foreach (var root in roots) {
      foreach (var n in Ast.Descendants(root).Prepend(root)) {
        // Ancestors come first, so a range keeps its outermost node.
        index.TryAdd(Key(n), n);
      }
    }
  }

  static List<Method> MethodsOf(DafnyProgram p, Uri file) =>
    Ast.Members(p.DefaultModuleDef).OfType<Method>()
      .Where(m => m is not Lemma && !m.IsGhost && m.Body != null && m.Origin.Uri == file).ToList();

  public void Apply(DafnyProgram resolvedProgram, DafnyProgram parsedProgram, Uri file) {
    var rms = MethodsOf(resolvedProgram, file);
    var pms = MethodsOf(parsedProgram, file);
    Index(resolved, rms);
    Index(parsed, pms);
    foreach (var m in pms) {
      annotated.Add(m.Name);
      if (m.Ins.Concat(m.Outs).Any(f => f.Name == Counter)
          || Ast.Descendants(m.Body).OfType<VarDeclStmt>().SelectMany(d => d.Locals).Any(v => v.Name == Counter)) {
        throw new InvalidOperationException($"{m.Name} already declares {Counter}; pick another counter name");
      }
    }
    foreach (var m in pms) {
      var o = m.Origin;
      m.Outs.Add(new Formal(o, Counter, new UserDefinedType(o, "nat", null), false, true, null, null));
      var created = new HashSet<Statement>();
      foreach (var b in Ast.Descendants(m.Body).OfType<BlockStmt>().Prepend(m.Body).ToList()) {
        Rewrite(b, created);
      }
      var init = Charge(o, Lit(o, 0), assign: true);
      m.Body.Body.Insert(0, init);
    }
  }

  void Rewrite(BlockStmt b, HashSet<Statement> created) {
    var body = new List<Statement>();
    foreach (var s in b.Body) {
      if (created.Contains(s) || !resolved.TryGetValue(Key(s), out var n) || n is not Statement a) {
        if (!created.Contains(s)) {
          Notes.Add($"line {Ast.Line(s)}: no resolved statement for {s.GetType().Name}; not charged");
        }
        body.Add(s);
        continue;
      }
      var o = s.Origin;
      var own = OwnCost(a);
      if (!own.IsZero) {
        body.Add(Mark(created, Charge(o, own.ToExpr(o))));
      }
      if (s is ReturnStmt { Rhss: { } rhss }) {
        rhss.Add(new ExprRhs(new NameSegment(o, Counter, null)));   // `return x` returns the counter too
      }
      body.Add(s);
      if (CalleeOf(a) is { } callee && annotated.Contains(callee)) {
        var t = $"s{temps++}";
        if (!AddCallLhs(s, t, created, body)) {
          Notes.Add($"line {Ast.Line(s)}: call to {callee} in a {s.GetType().Name}; its steps are not added");
        } else {
          body.Add(Mark(created, Charge(o, new NameSegment(o, t, null))));
        }
      }
      if (a is WhileStmt w && s is WhileStmt pw && pw.Body != null) {
        var guard = Cost(w.Guard);
        var iter = new Cost { Const = 1 };
        iter.Add(guard);
        pw.Body.Body.Insert(0, Mark(created, Charge(o, iter.ToExpr(o))));
        if (!guard.IsZero) {
          body.Add(Mark(created, Charge(o, guard.ToExpr(o))));
        }
      } else if (s is ForLoopStmt pf && pf.Body != null) {
        pf.Body.Body.Insert(0, Mark(created, Charge(o, Lit(o, 1))));
      }
    }
    b.Body.Clear();
    b.Body.AddRange(body);
  }

  static Statement Mark(HashSet<Statement> created, Statement s) {
    created.Add(s);
    return s;
  }

  /// `steps := steps + e`, or `steps := e` with `assign`.
  Statement Charge(IOrigin o, Expression e, bool assign = false) {
    var rhs = assign ? e : new BinaryExpr(o, BinaryExpr.Opcode.Add, new NameSegment(o, Counter, null), e);
    return new AssignStatement(o, [new NameSegment(o, Counter, null)], [new ExprRhs(rhs)]);
  }

  static Expression Lit(IOrigin o, int v) => new LiteralExpr(o, v);

  /// Add a ghost lhs `t` to a call statement, declaring it where needed.
  bool AddCallLhs(Statement s, string t, HashSet<Statement> created, List<Statement> body) {
    var o = s.Origin;
    switch (s) {
      case VarDeclStmt { Assign: AssignStatement a } d:
        d.Locals.Add(new LocalVariable(o, t, null, false));
        a.Lhss.Add(new AutoGhostIdentifierExpr(o, t));
        return true;
      case AssignStatement a:
        body.Insert(body.Count - 1, Mark(created,
          new VarDeclStmt(o, [new LocalVariable(o, t, new UserDefinedType(o, "nat", null), true)], null)));
        a.Lhss.Add(new NameSegment(o, t, null));
        return true;
      default:
        return false;
    }
  }

  static string CalleeOf(Statement a) {
    var call = a switch {
      VarDeclStmt { Assign: AssignStatement u } => u.ResolvedStatements?.OfType<CallStmt>().FirstOrDefault(),
      AssignStatement u => u.ResolvedStatements?.OfType<CallStmt>().FirstOrDefault(),
      _ => null,
    };
    return call?.Method.Name;
  }

  /// What a statement's own expressions cost, its nested statements excluded.
  Cost OwnCost(Statement a) {
    var c = new Cost();
    if (a.IsGhost) {
      return c;
    }
    switch (a) {
      case VarDeclStmt { Assign: AssignStatement u }:
        return OwnCost(u);
      case VarDeclStmt:
        return c;
      case AssignStatement u:
        foreach (var r in u.ResolvedStatements ?? []) {
          switch (r) {
            case SingleAssignStmt sa:
              if (sa.Lhs.Resolved is not IdentifierExpr) {
                c.Add(Cost(sa.Lhs));
              }
              if (sa.Rhs is ExprRhs er) {
                c.Add(Cost(er.Expr));
              } else if (sa.Rhs is not HavocRhs) {
                Notes.Add($"line {Ast.Line(a)}: {sa.Rhs.GetType().Name} not charged");
              }
              break;
            case CallStmt cs:
              foreach (var arg in cs.Args) {
                c.Add(Cost(arg));
              }
              break;
          }
        }
        return c;
      case IfStmt i:
        return Cost(i.Guard);
      case ForLoopStmt f:
        c.Add(Cost(f.Start));
        c.Add(Cost(f.End));
        return c;
      case ReturnStmt r:
        foreach (var rhs in r.Rhss ?? []) {
          if (rhs is ExprRhs er) {
            c.Add(Cost(er.Expr));
          }
        }
        return c;
      case PrintStmt p:
        foreach (var e in p.Args) {
          c.Add(Cost(e));
        }
        return c;
      case WhileStmt or BlockStmt or BreakOrContinueStmt:
        return c;   // a loop's guard is charged per iteration, in the body
      default:
        Notes.Add($"line {Ast.Line(a)}: {a.GetType().Name} not charged");
        return c;
    }
  }

  /// The cost of evaluating a resolved expression, per COMPLEXITY.md.
  Cost Cost(Expression a) {
    var c = new Cost();
    if (a == null) {
      return c;
    }
    var e = a.Resolved ?? a;
    switch (e) {
      case LiteralExpr or IdentifierExpr or ThisExpr or WildcardExpr:
        return c;
      case BinaryExpr b when b.ResolvedOp is BinaryExpr.ResolvedOpcode.And or BinaryExpr.ResolvedOpcode.Or
                                or BinaryExpr.ResolvedOpcode.Imp: {
          // Short-circuit: the right operand is evaluated only on one outcome.
          c.Const = 1;
          c.Add(Cost(b.E0));
          var right = Cost(b.E1);
          if (!right.IsZero && Clone(b.E0) is { } test) {
            var o = b.Origin;
            var ran = b.ResolvedOp == BinaryExpr.ResolvedOpcode.Or ? Lit(o, 0) : right.ToExpr(o);
            var skipped = b.ResolvedOp == BinaryExpr.ResolvedOpcode.Or ? right.ToExpr(o) : Lit(o, 0);
            c.Terms.Add(new ITEExpr(o, false, test, ran, skipped));
          } else {
            c.Add(right);
          }
          return c;
        }
      case BinaryExpr b when b.ResolvedOp == BinaryExpr.ResolvedOpcode.Concat:
        c.Add(Cost(b.E0));
        c.Add(Cost(b.E1));
        AddLength(c, b.E1, b);   // `s + t` costs |t|
        return c;
      case ITEExpr ite: {
          c.Const = 1;
          c.Add(Cost(ite.Test));
          var thn = Cost(ite.Thn);
          var els = Cost(ite.Els);
          if ((!thn.IsZero || !els.IsZero) && Clone(ite.Test) is { } test) {
            c.Terms.Add(new ITEExpr(ite.Origin, false, test, thn.ToExpr(ite.Origin), els.ToExpr(ite.Origin)));
          }
          return c;
        }
      case FunctionCallExpr f:
        foreach (var arg in f.Args) {
          c.Add(Cost(arg));
        }
        c.Add(CallCost(f));
        return c;
      case MemberSelectExpr m when m.MemberName is "Keys" or "Values" or "Items":
        c.Add(Cost(m.Obj));
        AddLength(c, m.Obj, m);
        return c;
      case SeqDisplayExpr or SetDisplayExpr or MapDisplayExpr or MultiSetDisplayExpr:
        foreach (var sub in e.SubExpressions) {
          c.Add(Cost(sub));
          c.Const += 1;
        }
        return c;
      case SeqConstructionExpr sc:
        c.Add(Cost(sc.N));
        AddTerm(c, sc.N, sc);
        Notes.Add($"line {Ast.Line(sc)}: seq(n, f) charged n; f's own cost not counted");
        return c;
      case ComprehensionExpr or LambdaExpr or LetExpr or MatchExpr:
        Notes.Add($"line {Ast.Line(e)}: {e.GetType().Name} charged 1");
        c.Const = 1;
        return c;
      case BinaryExpr or UnaryOpExpr or SeqSelectExpr or SeqUpdateExpr or MultiSelectExpr
        or ConversionExpr or MemberSelectExpr or DatatypeValue:
        c.Const = 1;
        foreach (var sub in e.SubExpressions) {
          c.Add(Cost(sub));
        }
        return c;
      default:
        Notes.Add($"line {Ast.Line(e)}: {e.GetType().Name} charged 1");
        c.Const = 1;
        foreach (var sub in e.SubExpressions) {
          c.Add(Cost(sub));
        }
        return c;
    }
  }

  /// A prelude function's charge from the COMPLEXITY.md table; a row's own
  /// function is charged 1 and noted.
  Cost CallCost(FunctionCallExpr f) {
    var c = new Cost();
    var args = f.Args;
    var o = f.Origin;
    if (f.Function.EnclosingClass?.EnclosingModuleDefinition?.Name != "Prelude") {
      Notes.Add($"line {Ast.Line(f)}: row function {f.Function.Name} charged 1; the model needs its cost");
      c.Const = 1;
      return c;
    }
    Expression Arg(int i) => Clone(args[i]);
    Expression Len(Expression x) => x == null ? null : new UnaryOpExpr(o, UnaryOpExpr.Opcode.Cardinality, x);
    Expression Call(string name, params Expression[] xs) =>
      xs.Any(x => x == null) ? null
        : new ApplySuffix(o, null, new NameSegment(o, name, null), xs.Select(x => new ActualBinding(null, x)).ToList(), null);
    var term = f.Function.Name switch {
      "IntToString" => Call("Digits", Arg(0)),
      "Join" => Sum(o, Call("SumLen", Arg(0)), Len(Arg(0))),
      "JoinInts" => Sum(o, Call("SumDigits", Arg(0)), Len(Arg(0))),
      "ParseInt" or "SplitWs" or "MaxSeq" or "MinSeq" or "SumSeq" or "ReplaceAll" => Len(Arg(0)),
      "ParseInts" => Call("SumLen", Arg(0)),
      "Sort" or "SortInts" or "SortStrings" => Call("SortCost", Len(Arg(0))),
      "Gcd" => Call("GcdSteps", Arg(0), Arg(1)),
      "Repeat" => Arg(0) is { } s && Arg(1) is { } n ? new BinaryExpr(o, BinaryExpr.Opcode.Mul, Len(s), n) : null,
      _ => Lit(o, 1),
    };
    if (term == null) {
      Notes.Add($"line {Ast.Line(f)}: {f.Function.Name}: argument not found in the parse tree; charged 1");
      term = Lit(o, 1);
    }
    c.Terms.Add(term);
    return c;
  }

  static Expression Sum(IOrigin o, Expression a, Expression b) =>
    a == null || b == null ? null : new BinaryExpr(o, BinaryExpr.Opcode.Add, a, b);

  void AddLength(Cost c, Expression of, Expression at) {
    if (Clone(of) is { } x) {
      c.Terms.Add(new UnaryOpExpr(at.Origin, UnaryOpExpr.Opcode.Cardinality, x));
    } else {
      Notes.Add($"line {Ast.Line(at)}: length operand not found in the parse tree; charged 1");
      c.Const += 1;
    }
  }

  void AddTerm(Cost c, Expression x, Expression at) {
    if (Clone(x) is { } y) {
      c.Terms.Add(y);
    } else {
      Notes.Add($"line {Ast.Line(at)}: operand not found in the parse tree; charged 1");
      c.Const += 1;
    }
  }

  /// A fresh parse-tree copy of the expression with the same source range.
  Expression Clone(Expression resolvedExpr) =>
    parsed.TryGetValue(Key(resolvedExpr), out var n) && n is Expression e ? new Cloner().CloneExpr(e) : null;
}

/// A sum: a constant plus expressions.
public class Cost {
  public int Const;
  public readonly List<Expression> Terms = [];

  public bool IsZero => Const == 0 && Terms.Count == 0;

  public void Add(Cost c) {
    Const += c.Const;
    Terms.AddRange(c.Terms);
  }

  public Expression ToExpr(IOrigin o) {
    Expression e = Const != 0 || Terms.Count == 0 ? new LiteralExpr(o, Const) : null;
    foreach (var t in Terms) {
      e = e == null ? t : new BinaryExpr(o, BinaryExpr.Opcode.Add, e, t);
    }
    return e;
  }
}
