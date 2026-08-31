// 299_B. Ksusha the Squirrel  (problem 641, solution 641_31)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,k=list(map(int,input().split()))
// 
// 
// 
// a=input().split('.')
// u=0
// 
// 
// 
// for i in range(len(a)):
//     if '#' in a[i]:
//         if len(a[i])+1>k:
//             print('NO')
//             u+=1
//             break
//     if u>0:
//         break
// 
// if u==0:
//     print('YES')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, s: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
