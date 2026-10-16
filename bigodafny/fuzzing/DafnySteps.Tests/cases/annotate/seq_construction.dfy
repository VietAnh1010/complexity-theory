// seq(n, f): 1 per element plus f's cost for each. A constant-cost lambda
// gives (1 + k) * n; a lambda whose cost depends on its argument gives
// n + SumSeq(seq(n, ...)).
include "../../../../prelude.dfy"
import opened Prelude

method Solve(a: seq<int>, n: nat) returns (output: seq<string>)
{
  var zeros := seq(n + 1, _ => 0);
  var evens := seq(n, i => i * 2);
  var texts := seq(|a|, j requires 0 <= j < |a| => IntToString(a[j]));
  output := texts;
}
