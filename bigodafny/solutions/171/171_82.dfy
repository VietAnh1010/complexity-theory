// 1328_A. Divisibility Problem  (problem 171, solution 171_82)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// num = int(input())
// 
// for i in range(num):
//     l = input().split()
//     a = int(l[0])
//     b = int(l[1])
// 
//     if a % b == 0:
//         print(0)
//     else:
//         print(int(b - (a % b)))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
