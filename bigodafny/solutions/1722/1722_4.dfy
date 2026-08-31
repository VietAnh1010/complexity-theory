// 887_B. Cubes for Masha  (problem 1722, solution 1722_4)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def gen(cur, used, x):
//     pos.add(cur)
//     if x == n:
//         return
//     for j in range(n):
//         if not used[j]:
//             for i in a[j]:
//                 if i != 0 or x != 0:
//                     used[j] = True
//                     gen(cur * 10 + i, used, x + 1)
//                     used[j] = False
// 
// 
// n = int(input())
// a = []
// for i in range(n):
//     a.append(list(map(int, input().split())))
// pos = set()
// gen(0, [False] * n, 0)
// x = 1
// while x in pos:
//     x += 1
// print(x - 1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, lists: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
