// 1463_A. Dungeon  (problem 2870, solution 2870_46)
// time complexity: O(n*m)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// for i in range(n):
//     s = list(map(int, input().split()))
//     d = sum(s)
//     if min(s) >= d // 9 and d % 9 == 0:
//         print('YES')
//     else:
//         print('NO')
//         
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, values_list: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
