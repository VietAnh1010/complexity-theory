// 799_A. Carrot Cakes  (problem 2773, solution 2773_68)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,t,k,d = list(map(int,input().split()))
// fi = ((n+k-1)//k) * t
// t1 = 0
// t2 = d
// while n > 0:
//     n -= k
//     t1 += t
//     if n <= 0:
//         break
//     if t1 > d:
//         n-=k
//         t2+=t
//         if n <= 0:
//             break
// if t1 < fi or (t2 < fi and t2 != d):
//     print("YES")
// else:
//     print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c: int, d: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
