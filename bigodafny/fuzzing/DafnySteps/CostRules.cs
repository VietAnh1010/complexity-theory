// Cost rules beyond COMPLEXITY.md's table, each enabled by name:
//   DafnySteps annotate IN.dfy OUT.dfy enable=functions,seq,arrays
// CostModel asks each enabled rule for an expression (or an array
// allocation) its table does not cover. To add a rule: implement ICostRule,
// add it to Annotate.Rules.
using Microsoft.Dafny;

namespace DafnySteps;

public interface ICostRule {
  /// The cost of `node`, or null when this rule does not handle it.
  Cost TryCost(INode node, CostModel model);
}

/// `functions`: a call F(x) to a function of the row costs F_steps(x).
/// F_steps is a generated ghost function with F's parameters, requires and
/// decreases; its body is the cost of F's body, so a recursive call costs
/// F_steps again.
public class FunctionsRule(string counter) : ICostRule {
  readonly Dictionary<string, string> costFunctions = [];

  public Cost TryCost(INode node, CostModel model) {
    if (node is not FunctionCallExpr f || !costFunctions.TryGetValue(f.Function.Name, out var name)) {
      return null;
    }
    var c = model.OfAll(f.Args);
    c.Terms.Add(CostModel.Call(f.Origin, name, f.Args.Select(model.Copy).ToArray()));
    return c;
  }

  /// Insert F_steps after each function F in `functions`. `declared` holds
  /// the names the program declares, to refuse a clash.
  public void AddCostFunctions(List<Function> functions, CostModel model, HashSet<string> declared,
                               Func<Function, Function> resolvedOf) {
    foreach (var f in functions) {
      var name = $"{f.Name}_{counter}";
      if (declared.Contains(name)) {
        throw new InvalidOperationException($"{name} is already declared; pick another counter name");
      }
      costFunctions[f.Name] = name;
    }
    foreach (var f in functions) {
      var o = f.Origin;
      var cloner = new Cloner();
      var cost = new Function(o, new Name(o, costFunctions[f.Name]), f.HasStaticKeyword, true, false,
        f.TypeArgs.Select(cloner.CloneTypeParam).ToList(), f.Ins.Select(p => cloner.CloneFormal(p, false)).ToList(),
        null, new UserDefinedType(o, "nat", null), f.Req.Select(cloner.CloneAttributedExpr).ToList(),
        new Specification<FrameExpression>([], null), [], cloner.CloneSpecExpr(f.Decreases),
        model.Of(resolvedOf(f).Body).ToExpr(o), null, null, null, null);
      var members = ((TopLevelDeclWithMembers)f.EnclosingClass).Members;
      members.Insert(members.IndexOf(f) + 1, cost);
    }
  }
}

/// `seq`: seq(n, i => e) costs n plus e's cost for each i (PerElement).
public class SeqRule : ICostRule {
  public Cost TryCost(INode node, CostModel model) {
    if (node is not SeqConstructionExpr sc || (sc.Initializer.Resolved ?? sc.Initializer) is not LambdaExpr lambda) {
      return null;
    }
    var c = model.Of(sc.N);
    c.Terms.Add(PerElement.Cost(model, sc.Origin, () => model.Copy(sc.N), lambda));
    return c;
  }
}

/// `arrays`: `new T[n]` costs n, `new T[n, m]` n * m; `new T[n](i => e)` is
/// charged like seq(n, i => e); `new T[] [a, b]` like a display.
public class ArraysRule : ICostRule {
  public Cost TryCost(INode node, CostModel model) {
    if (node is not AllocateArray a) {
      return null;
    }
    if (a.InitDisplay != null) {
      return model.OfElements(a.InitDisplay);
    }
    var o = a.Origin;
    Expression Size() => a.ArrayDimensions.Select(model.Copy).Aggregate((x, y) => CostModel.Multiply(o, x, y));
    var c = model.OfAll(a.ArrayDimensions);
    if (a.ElementInit == null) {
      c.Terms.Add(Size());
    } else if (a.ArrayDimensions.Count == 1 && (a.ElementInit.Resolved ?? a.ElementInit) is LambdaExpr lambda) {
      c.Terms.Add(PerElement.Cost(model, o, Size, lambda));
    } else {
      return null;
    }
    return c;
  }
}

static class PerElement {
  /// n elements, each 1 plus the cost of `lambda`'s body: (1 + k) * n when the
  /// body costs a constant k, else n + SumSeq(seq(n, i => <cost of body>)).
  /// `n` makes a fresh copy of the count each call.
  public static Expression Cost(CostModel model, IOrigin o, Func<Expression> n, LambdaExpr lambda) {
    var body = model.Of(lambda.Body);
    if (body.Terms.Count == 0) {
      return body.Const == 0 ? n() : CostModel.Multiply(o, new LiteralExpr(o, 1 + body.Const), n());
    }
    var parsed = (LambdaExpr)model.Copy(lambda);
    var perElement = new LambdaExpr(o, parsed.BoundVars, parsed.Range,
      new Specification<FrameExpression>([], null), body.ToExpr(o), null);
    return CostModel.Add(o, n(), CostModel.Call(o, "SumSeq", new SeqConstructionExpr(o, null, n(), perElement)));
  }
}
