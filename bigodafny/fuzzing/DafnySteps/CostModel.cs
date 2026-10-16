// The cost model of COMPLEXITY.md, applied to resolved expressions.
//
// Of(e) is what evaluating `e` costs: a constant plus terms. A term is an
// expression to insert into the annotated program, such as `|t|` for `s + t`.
// It is built from the parse tree, by copying the node with the same source
// range as the resolved one.
//
// The model charges only what COMPLEXITY.md's table covers. Any other
// expression goes to the enabled rules (CostRules.cs); if none applies, Of
// throws Unsupported, so a charge is never silently wrong.
using Microsoft.Dafny;

namespace DafnySteps;

/// A cost: a constant plus expression terms.
public class Cost {
  public int Const;
  public readonly List<Expression> Terms = [];

  public bool IsZero => Const == 0 && Terms.Count == 0;

  public void Add(Cost c) {
    Const += c.Const;
    Terms.AddRange(c.Terms);
  }

  /// `Const + t1 + t2 ..`, the constant left out when it is 0.
  public Expression ToExpr(IOrigin o) {
    Expression e = Const != 0 || Terms.Count == 0 ? new LiteralExpr(o, Const) : null;
    foreach (var t in Terms) {
      e = e == null ? t : new BinaryExpr(o, BinaryExpr.Opcode.Add, e, t);
    }
    return e;
  }
}

/// Code the model cannot charge; `rule` names the rule that would.
public class Unsupported(INode at, string what, string rule = null)
  : InvalidOperationException($"line {Ast.Line(at)}: {what} is not in the cost model"
                              + (rule == null ? "" : $" (use enable={rule})"));

public class CostModel(Dictionary<(int, int), INode> parsedByRange, List<ICostRule> rules) {
  public Cost Of(Expression expression) {
    if (expression == null) {
      return new Cost();
    }
    var e = expression.Resolved ?? expression;
    return e switch {
      LiteralExpr or IdentifierExpr or ThisExpr or WildcardExpr => new Cost(),
      BinaryExpr { ResolvedOp: BinaryExpr.ResolvedOpcode.And or BinaryExpr.ResolvedOpcode.Or
                   or BinaryExpr.ResolvedOpcode.Imp } b => OfShortCircuit(b),
      BinaryExpr { ResolvedOp: BinaryExpr.ResolvedOpcode.Concat } b => OfConcat(b),
      ITEExpr ite => OfConditional(ite),
      FunctionCallExpr { Function.EnclosingClass.EnclosingModuleDefinition.Name: "Prelude" } f => OfPreludeCall(f),
      MemberSelectExpr { MemberName: "Keys" or "Values" or "Items" } m => OfMapView(m),
      SeqDisplayExpr or SetDisplayExpr or MapDisplayExpr or MultiSetDisplayExpr => OfDisplay(e),
      BinaryExpr or UnaryOpExpr or SeqSelectExpr or SeqUpdateExpr or MultiSelectExpr
        or ConversionExpr or MemberSelectExpr or DatatypeValue => OnePlusOperands(e),
      LambdaExpr => new Cost(),   // its body is charged where it is called
      StmtExpr s => Of(s.E),      // the statement is ghost
      LetExpr { Exact: true } let => OfLet(let),
      _ => ByRule(e),
    };
  }

  /// The right-hand side of an assignment.
  public Cost OfRhs(AssignmentRhs rhs) => rhs switch {
    ExprRhs r => Of(r.Expr),
    HavocRhs => new Cost(),
    _ => ByRule(rhs),
  };

  /// The first enabled rule's cost for `n`; Unsupported if none applies.
  Cost ByRule(INode n) =>
    rules.Select(r => r.TryCost(n, this)).FirstOrDefault(c => c != null) ?? throw n switch {
      FunctionCallExpr f => new Unsupported(n, $"call to {f.Function.Name}", "functions"),
      SeqConstructionExpr => new Unsupported(n, "seq(n, f)", "seq"),
      AllocateArray => new Unsupported(n, "new array", "arrays"),
      _ => new Unsupported(n, n.GetType().Name),
    };

  /// `var x := e; body`: e, plus body. The body's cost keeps the binding,
  /// since it may mention x.
  Cost OfLet(LetExpr let) {
    var c = new Cost();
    foreach (var rhs in let.RHSs) {
      c.Add(Of(rhs));
    }
    var body = Of(let.Body);
    c.Const += body.Const;
    if (body.Terms.Count > 0) {
      if (Copy(let) is not LetExpr parsed) {
        throw new Unsupported(let, "a let missing from the parse tree");
      }
      var terms = new Cost();
      terms.Terms.AddRange(body.Terms);
      c.Terms.Add(new LetExpr(let.Origin, parsed.LHSs, parsed.RHSs, terms.ToExpr(let.Origin), true, null));
    }
    return c;
  }

  /// `a && b`: 1, plus a, plus b only when a lets b run.
  Cost OfShortCircuit(BinaryExpr b) {
    var c = new Cost { Const = 1 };
    c.Add(Of(b.E0));
    var right = Of(b.E1);
    if (!right.IsZero && Copy(b.E0) is { } test) {
      var o = b.Origin;
      var isOr = b.ResolvedOp == BinaryExpr.ResolvedOpcode.Or;
      Expression zero = new LiteralExpr(o, 0);
      c.Terms.Add(new ITEExpr(o, false, test, isOr ? zero : right.ToExpr(o), isOr ? right.ToExpr(o) : zero));
    } else {
      c.Add(right);
    }
    return c;
  }

  /// `s + t` on sequences: the operands, plus |t|.
  Cost OfConcat(BinaryExpr b) {
    var c = Of(b.E0);
    c.Add(Of(b.E1));
    c.Terms.Add(Length(b.Origin, Copy(b.E1)) ?? throw new Unsupported(b, "an operand missing from the parse tree"));
    return c;
  }

  /// `if t then x else y`: 1, plus t, plus the branch taken (both when the
  /// test cannot be copied).
  Cost OfConditional(ITEExpr ite) {
    var c = new Cost { Const = 1 };
    c.Add(Of(ite.Test));
    var thn = Of(ite.Thn);
    var els = Of(ite.Els);
    if (thn.IsZero && els.IsZero) {
      return c;
    }
    if (Copy(ite.Test) is { } test) {
      c.Terms.Add(new ITEExpr(ite.Origin, false, test, thn.ToExpr(ite.Origin), els.ToExpr(ite.Origin)));
    } else {
      c.Add(thn);
      c.Add(els);
    }
    return c;
  }

  /// A prelude function: the arguments, plus COMPLEXITY.md's charge.
  Cost OfPreludeCall(FunctionCallExpr f) {
    var c = new Cost();
    foreach (var arg in f.Args) {
      c.Add(Of(arg));
    }
    var o = f.Origin;
    Expression Arg(int i) => Copy(f.Args[i]);
    var term = f.Function.Name switch {
      "IntToString" => Call(o, "Digits", Arg(0)),
      "Join" => Add(o, Call(o, "SumLen", Arg(0)), Length(o, Arg(0))),
      "JoinInts" => Add(o, Call(o, "SumDigits", Arg(0)), Length(o, Arg(0))),
      "ParseInt" or "SplitWs" or "MaxSeq" or "MinSeq" or "SumSeq" or "ReplaceAll" => Length(o, Arg(0)),
      "ParseInts" => Call(o, "SumLen", Arg(0)),
      "Sort" or "SortInts" or "SortStrings" => Call(o, "SortCost", Length(o, Arg(0))),
      "Gcd" => Call(o, "GcdSteps", Arg(0), Arg(1)),
      "Repeat" => Multiply(o, Length(o, Arg(0)), Arg(1)),
      _ => new LiteralExpr(o, 1),
    };
    c.Terms.Add(term ?? throw new Unsupported(f, $"{f.Function.Name} with an argument missing from the parse tree"));
    return c;
  }

  /// `m.Keys`, `m.Values`, `m.Items`: |m|.
  Cost OfMapView(MemberSelectExpr m) {
    var c = Of(m.Obj);
    c.Terms.Add(Length(m.Origin, Copy(m.Obj)) ?? throw new Unsupported(m, "a map missing from the parse tree"));
    return c;
  }

  /// `[a, b, c]`: the elements, plus 1 per element.
  Cost OfDisplay(Expression e) {
    var c = new Cost();
    foreach (var element in e.SubExpressions) {
      c.Add(Of(element));
      c.Const += 1;
    }
    return c;
  }

  Cost OnePlusOperands(Expression e) {
    var c = new Cost { Const = 1 };
    foreach (var operand in e.SubExpressions) {
      c.Add(Of(operand));
    }
    return c;
  }

  /// A fresh copy of the parse-tree node with the same source range, or null.
  public Expression Copy(Expression resolved) =>
    parsedByRange.TryGetValue(Ast.Range(resolved), out var node) && node is Expression e
      ? new Cloner().CloneExpr(e) : null;

  // Expression builders. Each returns null when an operand is null.

  public static Expression Length(IOrigin o, Expression x) =>
    x == null ? null : new UnaryOpExpr(o, UnaryOpExpr.Opcode.Cardinality, x);

  public static Expression Add(IOrigin o, Expression a, Expression b) =>
    a == null || b == null ? null : new BinaryExpr(o, BinaryExpr.Opcode.Add, a, b);

  public static Expression Multiply(IOrigin o, Expression a, Expression b) =>
    a == null || b == null ? null : new BinaryExpr(o, BinaryExpr.Opcode.Mul, a, b);

  public static Expression Call(IOrigin o, string function, params Expression[] args) =>
    args.Any(x => x == null) ? null
      : new ApplySuffix(o, null, new NameSegment(o, function, null),
          args.Select(x => new ActualBinding(null, x)).ToList(), null);
}
