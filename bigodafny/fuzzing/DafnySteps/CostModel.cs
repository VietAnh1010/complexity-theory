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

  public static Cost Sum(IEnumerable<Cost> costs) {
    var sum = new Cost();
    foreach (var c in costs) {
      sum.Add(c);
    }
    return sum;
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
      SeqDisplayExpr or SetDisplayExpr or MapDisplayExpr or MultiSetDisplayExpr => OfElements(e.SubExpressions),
      BinaryExpr or UnaryOpExpr or SeqSelectExpr or SeqUpdateExpr or MultiSelectExpr
        or ConversionExpr or MemberSelectExpr or DatatypeValue => Plus(1, OfAll(e.SubExpressions)),
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

  public Cost OfAll(IEnumerable<Expression> es) => Cost.Sum(es.Select(Of));

  /// `[a, b, c]`: the elements, plus 1 per element.
  public Cost OfElements(IEnumerable<Expression> elements) =>
    Cost.Sum(elements.Select(x => Plus(1, Of(x))));

  /// The first enabled rule's cost for `n`; Unsupported if none applies.
  Cost ByRule(INode n) =>
    rules.Select(r => r.TryCost(n, this)).FirstOrDefault(c => c != null) ?? throw n switch {
      FunctionCallExpr f => new Unsupported(n, $"call to {f.Function.Name}", "functions"),
      SeqConstructionExpr => new Unsupported(n, "seq(n, f)", "seq"),
      AllocateArray => new Unsupported(n, "new array", "arrays"),
      _ => new Unsupported(n, n.GetType().Name),
    };

  /// `var x := e; body`: e, plus body. The body's terms keep the binding,
  /// since they may mention x.
  Cost OfLet(LetExpr let) {
    var c = OfAll(let.RHSs);
    var body = Of(let.Body);
    c.Const += body.Const;
    if (body.Terms.Count > 0) {
      var parsed = (LetExpr)Copy(let);
      body.Const = 0;
      c.Terms.Add(new LetExpr(let.Origin, parsed.LHSs, parsed.RHSs, body.ToExpr(let.Origin), true, null));
    }
    return c;
  }

  /// `a && b`, `a ==> b`: 1, plus a, plus b only when a holds; `a || b`:
  /// b only when a fails.
  Cost OfShortCircuit(BinaryExpr b) {
    var right = Of(b.E1);
    var none = new Cost();
    var isOr = b.ResolvedOp == BinaryExpr.ResolvedOpcode.Or;
    return Plus(1, Of(b.E0), isOr ? Branch(b.E0, none, right) : Branch(b.E0, right, none));
  }

  /// `if t then x else y`: 1, plus t, plus the branch taken.
  Cost OfConditional(ITEExpr ite) => Plus(1, Of(ite.Test), Branch(ite.Test, Of(ite.Thn), Of(ite.Els)));

  /// `if test then thn else els` as one term; both branches when `test` has
  /// no parse-tree copy (a desugared chain `a < b < c`).
  Cost Branch(Expression test, Cost thn, Cost els) {
    if (thn.IsZero && els.IsZero) {
      return new Cost();
    }
    if (TryCopy(test) is not { } t) {
      return Cost.Sum([thn, els]);
    }
    var o = test.Origin;
    var c = new Cost();
    c.Terms.Add(new ITEExpr(o, false, t, thn.ToExpr(o), els.ToExpr(o)));
    return c;
  }

  /// `s + t` on sequences: the operands, plus |t|.
  Cost OfConcat(BinaryExpr b) => Plus(Length(b.Origin, Copy(b.E1)), Of(b.E0), Of(b.E1));

  /// `m.Keys`, `m.Values`, `m.Items`: |m|.
  Cost OfMapView(MemberSelectExpr m) => Plus(Length(m.Origin, Copy(m.Obj)), Of(m.Obj));

  /// A prelude function: the arguments, plus COMPLEXITY.md's charge.
  Cost OfPreludeCall(FunctionCallExpr f) {
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
    return Plus(term, OfAll(f.Args));
  }

  /// A fresh copy of the parse-tree node with the same source range.
  public Expression Copy(Expression resolved) =>
    TryCopy(resolved) ?? throw new Unsupported(resolved, $"{resolved.GetType().Name} with no parse-tree copy");

  Expression TryCopy(Expression resolved) =>
    parsedByRange.TryGetValue(Ast.Range(resolved), out var node) && node is Expression e
      ? new Cloner().CloneExpr(e) : null;

  static Cost Plus(int k, params Cost[] parts) {
    var c = Cost.Sum(parts);
    c.Const += k;
    return c;
  }

  static Cost Plus(Expression term, params Cost[] parts) {
    var c = Cost.Sum(parts);
    c.Terms.Add(term);
    return c;
  }

  // Expression builders.

  public static Expression Length(IOrigin o, Expression x) => new UnaryOpExpr(o, UnaryOpExpr.Opcode.Cardinality, x);

  public static Expression Add(IOrigin o, Expression a, Expression b) => new BinaryExpr(o, BinaryExpr.Opcode.Add, a, b);

  public static Expression Multiply(IOrigin o, Expression a, Expression b) => new BinaryExpr(o, BinaryExpr.Opcode.Mul, a, b);

  public static Expression Call(IOrigin o, string function, params Expression[] args) =>
    new ApplySuffix(o, null, new NameSegment(o, function, null), args.Select(x => new ActualBinding(null, x)).ToList(), null);
}
