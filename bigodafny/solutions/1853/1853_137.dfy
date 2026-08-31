// 650_A. Watchmen  (problem 1853, solution 1853_137)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = []
// b = {}
// c = {}
// for i in range(n):
//     x, y = [int(d) for d in input().split()]
//     b[y] = 0
//     a.append((x, y))
// a.sort()
// b[a[0][1]] = 1
// c[a[0][1]] = 1
// summa = 0
// count = 1
// for i in range(1, n):
//     if a[i][0] == a[i - 1][0]:
//         summa += count
//         count += 1
//     else:
//         count = 1
//         c = {}
//     b[a[i][1]] += 1
//     if a[i][1] not in c:
//         c[a[i][1]] = 0
//     c[a[i][1]] += 1
//     summa = summa + b[a[i][1]] - c[a[i][1]]
// print(summa)
//         
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, coordinates: seq<(int, int)>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
