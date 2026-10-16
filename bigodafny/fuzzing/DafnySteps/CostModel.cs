// The cost model of COMPLEXITY.md, applied to resolved expressions.
//
// Of(e) is what evaluating `e` costs: a constant plus terms. A term is an
// expression to insert into the annotated program, such as `|t|` for `s + t`.
// It is built from the parse tree, by copying the node with the same source
// range as the resolved one. When no such node exists, the term is charged 1
// instead and a note says so.
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

public class CostModel(Dictionary<(int, int), INode> parsedByRange, List<string> notes) {
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
      FunctionCallExpr f => OfFunctionCall(f),
      MemberSelectExpr { MemberName: "Keys" or "Values" or "Items" } m => OfMapView(m),
      SeqDisplayExpr or SetDisplayExpr or MapDisplayExpr or MultiSetDisplayExpr => OfDisplay(e),
      SeqConstructionExpr sc => OfSeqConstruction(sc),
      ComprehensionExpr or LambdaExpr or LetExpr or MatchExpr => Unmodelled(e),
      BinaryExpr or UnaryOpExpr or SeqSelectExpr or SeqUpdateExpr or MultiSelectExpr
        or ConversionExpr or MemberSelectExpr or DatatypeValue => OnePlusOperands(e),
      _ => NotedOnePlusOperands(e),
    };
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
    AddLength(c, b.E1, b);
    return c;
  }

  /// `if t then x else y`: 1, plus t, plus the branch taken.
  Cost OfConditional(ITEExpr ite) {
    var c = new Cost { Const = 1 };
    c.Add(Of(ite.Test));
    var thn = Of(ite.Thn);
    var els = Of(ite.Els);
    if ((!thn.IsZero || !els.IsZero) && Copy(ite.Test) is { } test) {
      c.Terms.Add(new ITEExpr(ite.Origin, false, test, thn.ToExpr(ite.Origin), els.ToExpr(ite.Origin)));
    }
    return c;
  }

  Cost OfFunctionCall(FunctionCallExpr f) {
    var c = new Cost();
    foreach (var arg in f.Args) {
      c.Add(Of(arg));
    }
    c.Add(OfCallee(f));
    return c;
  }

  /// `m.Keys`, `m.Values`, `m.Items`: |m|.
  Cost OfMapView(MemberSelectExpr m) {
    var c = Of(m.Obj);
    AddLength(c, m.Obj, m);
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

  /// `seq(n, f)`: n. The model has no charge for f; noted.
  Cost OfSeqConstruction(SeqConstructionExpr sc) {
    var c = Of(sc.N);
    if (Copy(sc.N) is { } n) {
      c.Terms.Add(n);
    } else {
      Note(sc, "operand not found in the parse tree; charged 1");
      c.Const += 1;
    }
    Note(sc, "seq(n, f) charged n; f's own cost not counted");
    return c;
  }

  Cost Unmodelled(Expression e) {
    Note(e, $"{e.GetType().Name} charged 1");
    return new Cost { Const = 1 };
  }

  Cost OnePlusOperands(Expression e) {
    var c = new Cost { Const = 1 };
    foreach (var operand in e.SubExpressions) {
      c.Add(Of(operand));
    }
    return c;
  }

  Cost NotedOnePlusOperands(Expression e) {
    Note(e, $"{e.GetType().Name} charged 1");
    return OnePlusOperands(e);
  }

  /// The callee's own charge: COMPLEXITY.md's table for a prelude function;
  /// 1 for a row's own function, noted.
  Cost OfCallee(FunctionCallExpr f) {
    var name = f.Function.Name;
    if (f.Function.EnclosingClass?.EnclosingModuleDefinition?.Name != "Prelude") {
      Note(f, $"row function {name} charged 1; the model needs its cost");
      return new Cost { Const = 1 };
    }
    var o = f.Origin;
    Expression Arg(int i) => Copy(f.Args[i]);
    var term = name switch {
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
    if (term == null) {
      Note(f, $"{name}: argument not found in the parse tree; charged 1");
      term = new LiteralExpr(o, 1);
    }
    var c = new Cost();
    c.Terms.Add(term);
    return c;
  }

  void AddLength(Cost c, Expression of, Expression at) {
    if (Copy(of) is { } x) {
      c.Terms.Add(Length(at.Origin, x));
    } else {
      Note(at, "length operand not found in the parse tree; charged 1");
      c.Const += 1;
    }
  }

  void Note(INode at, string text) => notes.Add($"line {Ast.Line(at)}: {text}");

  /// A fresh copy of the parse-tree node with the same source range, or null.
  Expression Copy(Expression resolved) =>
    parsedByRange.TryGetValue(Ast.Range(resolved), out var node) && node is Expression e
      ? new Cloner().CloneExpr(e) : null;

  // Expression builders. Each returns null when an operand is null, so a
  // missing copy propagates to OfCallee, which notes it.

  static Expression Length(IOrigin o, Expression x) =>
    x == null ? null : new UnaryOpExpr(o, UnaryOpExpr.Opcode.Cardinality, x);

  static Expression Add(IOrigin o, Expression a, Expression b) =>
    a == null || b == null ? null : new BinaryExpr(o, BinaryExpr.Opcode.Add, a, b);

  static Expression Multiply(IOrigin o, Expression a, Expression b) =>
    a == null || b == null ? null : new BinaryExpr(o, BinaryExpr.Opcode.Mul, a, b);

  static Expression Call(IOrigin o, string function, params Expression[] args) =>
    args.Any(x => x == null) ? null
      : new ApplySuffix(o, null, new NameSegment(o, function, null),
          args.Select(x => new ActualBinding(null, x)).ToList(), null);
}
