// 361_B. Levko and Permutation  (problem 2089, solution 2089_121)
// time complexity: O(n*m)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,k=map(int,input().split())
// if n==k:
//     print(-1)
// else:
//     a=[]
//     a.append(n-k)
//     for i in range(1,n-k):
//         a.append(i)
//     for j in range(n-k+1,n+1):
//         a.append(j)
//     print(*a)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
