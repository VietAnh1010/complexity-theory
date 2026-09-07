// 490_A. Team Olympiad  (problem 2610, solution 2610_51)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = [[] for i in range(3)]
// for i, x in enumerate(map(int, input().split()), 1):
//         a[x-1] += [i]
// k = min(len(a[0]), len(a[1]), len(a[2]))
// print(k)
// for i in range(k):
//         print(a[0][i], a[1][i], a[2][i])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
