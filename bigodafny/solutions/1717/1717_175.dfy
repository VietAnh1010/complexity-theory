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

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
