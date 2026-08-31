// 797_A. k-Factorization  (problem 310, solution 310_51)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, k=map(int, input().split())
// h=n
// t=""
// f=0
// i=2
// while k!=f+1 and i<=n/2:
//     if h%i==0:
//         f+=1
//         t+="{} ".format(i)
//         h=int(h/i)
//     else:
//         i+=1
// if k>f+1 or h==1:
//     print(-1)
// else:
//     print(t+"{}".format(h))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
