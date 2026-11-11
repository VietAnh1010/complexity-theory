// --- Python ---------------------------------------------------------
// from math import sqrt as S
// def ps(n):
//     return int(S(n))!=S(n)
// n=int(input())
// l=sorted([int(i) for i in input().split()])
// for i in l:
//     if i<0:
//         ans=i 
//     elif ps(i):
//         ans=i
// print(ans)
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

method Solve(n: int, a_list: seq<int>)
    returns (output: string, ghost steps: nat)
  ensures steps <= 2 * NLogN(|a_list|) + |a_list| * (6 * ISqrt(MaxOr(a_list)) + 12) + 3 + |output|
{
  steps := 0;
  steps := steps + SortCost(|a_list|);
  var l := SortInts(a_list);
  SortCostWithin(|a_list|, |a_list|);
  SortIntsKeepsElems(a_list);
  if |a_list| > 0 { MaxSeqBound(a_list); }
  assert forall x :: x in l ==> x <= MaxOr(a_list);
  ghost var K := 6 * ISqrt(MaxOr(a_list)) + 12;
  var ans := 0;
  var i := 0;
  while i < |l|
    invariant 0 <= i <= |l| && |l| == |a_list|
    invariant steps <= SortCost(|a_list|) + i * K
    decreases |l| - i
  {
    CostMulDistrib(i, 1, i + 1, K);
    steps := steps + 3;
    steps := steps + 1;
    var v := l[i];
    steps := steps + 1;
    if v < 0 {
      ans := v;
    } else {
      var r, s0 := IntSqrt2358(v);
      steps := steps + s0;
      assert l[i] in l;
      LeISqrt(r, MaxOr(a_list));
      steps := steps + 2;
      if r * r != v {
        ans := v;
      }
    }
    steps := steps + 1;
    i := i + 1;
  }
  steps := steps + 2;
  steps := steps + Digits(ans);
  output := IntToString(ans);
  IntToStringDigits(ans);
}

ghost function MaxOr(s: seq<int>): int
{
  if |s| > 0 then MaxSeq(s) else 0
}

method IntSqrt2358(x: int) returns (r: int, ghost steps: nat)
  ensures r >= 0 && (x >= 0 ==> r * r <= x) && steps == 6 * r + 4
{
  steps := 0;
  r := 0;
  while (r + 1) * (r + 1) <= x
    invariant r >= 0 && steps == 6 * r && (r == 0 || r * r <= x)
    decreases x - r
  {
    steps := steps + 5;
    steps := steps + 1;
    r := r + 1;
  }
  steps := steps + 4;
}

import opened Prelude
