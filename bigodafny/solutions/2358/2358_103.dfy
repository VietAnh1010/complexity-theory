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
  output := ""; // TODO: translate the Python above
}
