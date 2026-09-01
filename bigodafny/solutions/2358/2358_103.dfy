// 914_A. Perfect Squares  (problem 2358, solution 2358_103)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
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

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var l := SortInts(a_list);
  var ans := 0;
  var i := 0;
  while i < |l|
    decreases |l| - i
  {
    var v := l[i];
    if v < 0 {
      ans := v;
    } else {
      var r := IntSqrt2358(v);
      if r * r != v {
        ans := v;
      }
    }
    i := i + 1;
  }
  output := IntToString(ans);
}

method IntSqrt2358(x: int) returns (r: int)
{
  r := 0;
  while (r + 1) * (r + 1) <= x
    decreases x - r
  {
    r := r + 1;
  }
}
