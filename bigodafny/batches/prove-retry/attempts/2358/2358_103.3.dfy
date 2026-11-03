include "../../../../prelude.dfy"

ghost function MaxNonneg(a: seq<int>): nat
{
  if |a| == 0 then 0 else if MaxSeq(a) > 0 then MaxSeq(a) else 0
}

lemma SqGe(a: int)
  requires a >= 0
  ensures a <= a * a
{
  if a > 0 { CostMulMono(a as nat, 1, a as nat); }
}

method Solve(n: int, a_list: seq<int>)
    returns (output: string, ghost steps: nat)
  ensures steps <= 2 * NLogN(|a_list|) + |a_list| * (12 + 6 * MaxNonneg(a_list)) + 12 + |output|
{
  steps := 0;
  steps := steps + SortCost(|a_list|);
  var l := SortInts(a_list);
  SortCostWithin(|a_list|, |a_list|);
  SortIntsKeepsElems(a_list);
  ghost var M := MaxNonneg(a_list);
  if |a_list| > 0 { MaxSeqBound(a_list); }
  assert forall k :: 0 <= k < |l| ==> l[k] in a_list;
  ghost var K: nat := 12 + 6 * M;
  var ans := 0;
  var i := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant |l| == |a_list|
    invariant forall k :: 0 <= k < |l| ==> l[k] <= M
    invariant steps <= 2 * NLogN(|a_list|) + 1 + i * K
    decreases |l| - i
  {
    steps := steps + 3;
    steps := steps + 1;
    var v := l[i];
    steps := steps + 1;
    if v < 0 {
      ans := v;
    } else {
      var r, s0 := IntSqrt2358(v);
      steps := steps + s0;
      steps := steps + 2;
      if r * r != v {
        ans := v;
      }
    }
    steps := steps + 1;
    CostMulDistrib(i, 1, i + 1, K);
    i := i + 1;
  }
  steps := steps + 2;
  IntToStringDigits(ans);
  steps := steps + Digits(ans);
  output := IntToString(ans);
}

method IntSqrt2358(x: int) returns (r: int, ghost steps: nat)
  ensures x >= 0 ==> steps <= 6 * x + 4
{
  steps := 0;
  r := 0;
  while (r + 1) * (r + 1) <= x
    invariant 0 <= r
    invariant steps == 6 * r
    invariant x < 0 || r <= x
    decreases x - r
  {
    SqGe(r + 1);
    steps := steps + 5;
    steps := steps + 1;
    r := r + 1;
  }
  steps := steps + 4;
}

import opened Prelude
