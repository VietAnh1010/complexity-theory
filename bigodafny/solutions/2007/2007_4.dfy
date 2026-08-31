// 1095_D. Circular Dance  (problem 2007, solution 2007_4)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// if n == 3:
//     print(3, 2, 1)
//     exit()
// d = []
// d.append([0, 0])
// for i in range(n):
//     x, y = map(int, input().split())
//     d.append([x, y])
// x = 1
// ans = []
// ans.append(1)
// while True:
//     t = d[x][0]
//     if d[t][0] == d[x][1] or d[t][1] == d[x][1]:
//         ans.append(t)
//         ans.append(d[x][1])
//         x = d[x][1]
//     else:
//         ans.append(d[x][1])
//         ans.append(t)
//         x = t
//     if len(ans) >= n:
//         break
// print(*ans[:n])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, edges: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
