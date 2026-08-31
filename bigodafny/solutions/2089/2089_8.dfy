// 361_B. Levko and Permutation  (problem 2089, solution 2089_8)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// 
// n,k=map(int,input().split())
// if n<=k:
//     print(-1)
// else:
//     l=[n-k]
//     for i in range(2,n-k+1):
//         l.append(i-1)
//     for i in range(n-k+1,n+1):
//         l.append(i)
//     print(*l)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
