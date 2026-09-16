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
  var n := a;
  var m := b;
  var c := 0;
  var i := 0;
  while i <= n
    decreases n - i
  {
    var j := 0;
    while j <= m
      decreases m - j
    {
      if i * i + j == n && j * j + i == m {
        c := c + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  output := IntToString(c);
}
