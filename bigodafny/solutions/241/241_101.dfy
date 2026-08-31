// 1038_D. Slime  (problem 241, solution 241_101)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// a=list(map(int, input().split()))
// a.sort()
// if n==1:
//     print(a[0])
// else:
//     i=0
//     while i<n and a[i]<=0:
//         i+=1
//     if i==0:
//         print(sum(a)-2*a[0])
//     elif i==n:
//         print(2*a[-1]-sum(a))
//     else:
//         print(sum(a[i:])-sum(a[:i]))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
