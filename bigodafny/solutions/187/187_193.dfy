// 984_A. Game  (problem 187, solution 187_193)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// a=input().split()
// for i in range(n):
//     a[i]=int(a[i])
// a=sorted(a)
// if n%2==0:
//     print(a[(n//2)-1])
// else:
//     print(a[(n//2)])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
