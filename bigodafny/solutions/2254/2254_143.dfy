// 1092_A. Uniform String  (problem 2254, solution 2254_143)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// for i in range(int(input())):
//     n,k=map(int,input().split())
//     s=""
//     x=0
//     for i in range(0,n):
//         s=s+chr(x+97)
//         x+=1
//         x=x%k
//     print(s)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
