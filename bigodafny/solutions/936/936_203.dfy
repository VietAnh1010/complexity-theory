// 1108_A. Two distinct points  (problem 936, solution 936_203)
// time complexity: O(n*m)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// for a in range(n):
//     L=list(map(int,input().split()))
//     if(L[0]==L[2]):
//         print(L[0],L[2]+1)
//     else:
//         print(L[0],L[2])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, grid: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
