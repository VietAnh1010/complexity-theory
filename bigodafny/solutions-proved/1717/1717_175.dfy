// 300_A. Array  (problem 1717, solution 1717_175)
// time complexity: O(nlogn)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// (input())
// a=sorted(map(int,input().split()))
// b=[a.pop(0)]
// c=a[-1]>0 and [a.pop()] or [a.pop(0),a.pop(0)]
// for l in b,c,a:
//     print(len(l),*l)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function FormatLenAndElems(l: seq<int>): string
{
  if |l| == 0 then IntToString(0) else IntToString(|l|) + " " + JoinInts(l, " ")
}

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires |a_list| >= 3
  ensures steps <= 2 * |a_list| * (CeilLog2(|a_list|) + 1) + 4 * |a_list| + 20
{
  SortCostTreeBound(|a_list|);
  steps := 1 + SortCost(|a_list|);
  var sorted := SortInts(a_list);
  var b := [sorted[0]];
  var rest := sorted[1..];
  var c: seq<int>;
  var a: seq<int>;
  steps := steps + 2;
  if rest[|rest| - 1] > 0 {
    c := [rest[|rest| - 1]];
    a := rest[..|rest| - 1];
  } else {
    c := [rest[0], rest[1]];
    a := rest[2..];
  }
  steps := steps + 3;
  output := FormatLenAndElems(b) + "\n" + FormatLenAndElems(c) + "\n" + FormatLenAndElems(a);
  steps := steps + |b| + |c| + |a| + 6;
}
