// 1236_A. Stones  (problem 1578, solution 1578_481)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t=int(input())
// for i in range(t):
//     a,b,c=map(int,input().split())
//     n=min(b,c//2)
//     b-=n
//     m=min(a,b//2)
//     print((m+n)*3)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, matrix: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
