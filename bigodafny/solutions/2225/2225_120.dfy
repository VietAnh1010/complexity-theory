// 998_A. Balloons  (problem 2225, solution 2225_120)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = [int(i) for i in input().split()]
// res = []
// if n == 2 and a[0] == a[1]:
//     print("-1")
// elif n == 1:
//     print("-1")
// else:
//     for i in range(n):
//         if a[i] != sum(a)-a[i]:
//             #print("1")
//             res.append(i+1)
//             break
// if len(res)!=0:
//     print("1")
//     print(*res)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, dimensions: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
