include "../../prelude.dfy"
import opened Prelude

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

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * NLogN(|a_list|) + |a_list| * (12 + 6 * MaxNonneg(a_list)) + 12 + |output|
{
  var l := SortInts(a_list);
  steps := 1 + SortCost(|a_list|);
  SortCostWithin(|a_list|, |a_list|);
  SortIntsKeepsElems(a_list);
  ghost var M := MaxNonneg(a_list);
  if |a_list| > 0 { MaxSeqBound(a_list); }
  var ans := 0;
  var i := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant |l| == |a_list|
    invariant forall k :: 0 <= k < |l| ==> l[k] <= M
    invariant steps <= 1 + 2 * NLogN(|a_list|) + 1 + 2 + i * (12 + 6 * M)
    decreases |l| - i
  {
    var v := l[i];
    if v < 0 {
      ans := v;
      steps := steps + 5;
    } else {
      var r, st := IntSqrt2358(v);
      if r * r != v {
        ans := v;
      }
      steps := steps + 6 + st;
    }
    CostMulDistrib(i, 1, i + 1, 12 + 6 * M);
    i := i + 1;
  }
  output := IntToString(ans);
  IntToStringDigits(ans);
  steps := steps + |output|;
}

method IntSqrt2358(x: int) returns (r: int, ghost steps: nat)
  ensures x >= 0 ==> steps <= 6 * x + 4
{
  r := 0;
  steps := 4;
  while (r + 1) * (r + 1) <= x
    invariant 0 <= r
    invariant steps == 4 + 6 * r
    invariant x < 0 || r <= x
    decreases x - r
  {
    SqGe(r + 1);
    r := r + 1;
    steps := steps + 6;
  }
}
