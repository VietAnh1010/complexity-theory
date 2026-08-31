// 886_C. Petya and Catacombs  (problem 2505, solution 2505_30)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// data = list(map(int, input().split()))
// d = [False] * (n + 4)
// d[0] = True
// res = 1
// for i in range(n):
//     #print(d)
//     if d[data[i]]:
//         d[data[i]] = False
//         d[i + 1] = True
//     else:
//         d[i + 1] = True
//         res += 1
// #print(d)
// print(res)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, coordinates: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
