// 1285_D. Dr. Evil Underscores  (problem 1870, solution 1870_58)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// seq = sorted(list(map(int, input().split())))
// 
// #Left (inc), Right(exc), bit to check, value to add 
// queue = [(0,n,30,0)]
// best = 2 ** 30
// while queue:
//     l, r, b, v = queue.pop()
//     if b >= 0:
//         mask = 1 << b
//         
//         if not mask & seq[l] and mask & seq[r - 1]:
//             for i in range(l, r):
//                 if mask & seq[i]:
//                     queue.append((l,i,b - 1, v + mask))
//                     queue.append((i,r,b - 1, v + mask))
//                     break
//         else:
//             queue.append((l, r, b - 1, v))
//     else:
//         best = min(best, v)
//         
// print(best)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, values: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
