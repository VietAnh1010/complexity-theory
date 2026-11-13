// 459_B. Pashmak and Flowers  (problem 669, solution 669_107)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// x=int(input())
// s=[int(i) for i in input().split()]
// s.sort()
// a=min(s)
// b=max(s)
// if a==b:
//     print(0,int(x*(x-1)/2))
// else:
//     A=0
//     B=0
//     for i in s:
//         if i==a:
//             A+=1
//         if i==b:
//             B+=1
//     print(b-a,int(A*B))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires |a_list| > 0
  ensures steps <= 2 * NLogN(|a_list|) + 10 * |a_list| + 2 * |output| + 20
{
  steps := 1;
  var s := SortInts(a_list);
  steps := steps + SortCost(|a_list|);
  SortCostWithin(|a_list|, |a_list|);
  assert |s| == |a_list|;
  var mn := MinSeq(s);
  var mx := MaxSeq(s);
  steps := steps + 2 * |s| + 1;
  if mn == mx {
    output := "0 " + IntToString(n * (n - 1) / 2);
    IntToStringDigits(n * (n - 1) / 2);
    steps := steps + 6 + Digits(n * (n - 1) / 2);
  } else {
    var cntA := 0;
    var cntB := 0;
    var i := 0;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant steps <= 1 + SortCost(|a_list|) + 2 * |s| + 1 + 6 * i
      decreases |s| - i
    {
      if s[i] == mn { cntA := cntA + 1; }
      if s[i] == mx { cntB := cntB + 1; }
      i := i + 1;
      steps := steps + 6;
    }
    output := IntToString(mx - mn) + " " + IntToString(cntA * cntB);
    IntToStringDigits(mx - mn);
    IntToStringDigits(cntA * cntB);
    steps := steps + 6 + Digits(mx - mn) + Digits(cntA * cntB);
  }
}
