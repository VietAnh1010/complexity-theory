// 214_A. System of Equations  (problem 482, solution 482_543)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,m=map(int,input().split())
// c=0
// for i in range(0,n+1):
//     for j in range(0,m+1):
//         if(i**2+j==n and j**2+i==m):
//             c+=1
// print(c)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
