// 750_A. New Year and Hurry  (problem 704, solution 704_614)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #NEW YEAR AND HURRY
// 
// n,hrs = map(int,input().split())
// cnt = 0
// res = 0
// l = []
// 
// if hrs > 240:
//     print(0)
// else:
//     for i in range(1,n+1):
//         ans = 5*i
//         hrs += (ans) 
//         #print(i,hrs,ans)
//         if hrs <= 240:
//             cnt += 1
//         
// print(cnt)
//     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
