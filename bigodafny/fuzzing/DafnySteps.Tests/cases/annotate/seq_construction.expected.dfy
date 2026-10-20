// seq(n, f): 1 per element plus f's cost for each. A constant-cost lambda
// gives (1 + k) * n; a lambda whose cost depends on its argument gives
// n + SumSeq(seq(n, ...)).

include "../../../../prelude.dfy"

method Solve(a: seq<int>, n: nat)
    returns (output: seq<string>, ghost steps: nat)
{
  steps := 0;
  steps := steps + (1 + (n + 1));
  var zeros := seq(n + 1, _ /* _v0 */ => 0);
  steps := steps + 2 * n;
  var evens := seq(n, i => i * 2);
  steps := steps + (1 + (|a| + SumSeq(seq(|a|, j requires 0 <= j < |a| => 1 + Digits(a[j])))));
  var texts := seq(|a|, j requires 0 <= j < |a| => IntToString(a[j]));
  output := texts;
}

import opened Prelude
