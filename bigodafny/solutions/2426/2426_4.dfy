// 839_B. Game of the Rows  (problem 2426, solution 2426_4)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, k = map(int, input().split())
// seat = {4:n, 2:n*2, 1:0}
// extra1 = 0
// a = sorted(map(int, input().split()), reverse=True)
// 
// def sit(n, m):
//     num = min(seat[n], m)
//     seat[n] -= num
//     return m - num
// 
// for m in a:
//     p4 = m // 4
//     p3, p2, p1 = 0, 0, 0
//     if m%4 == 3:
//         p3 = 1
//     else:
//         p2 = int(m % 4 > 1)
//         p1 = int(m % 2)
// 
//     extra4 = sit(4, p4)
//     p2 += extra4*2
//     if sit(4, p3) > 0:
//         p2 += 1
//         p1 += 1
// 
//     extra2 = sit(2, p2)
//     x = sit(4, extra2)
//     seat[1] += extra2 - x
//     p1 += x * 2
// 
//     extra1 += p1
// 
// extra1 = sit(1, extra1)
// x = sit(4, extra1)
// seat[2] += extra1 - x
// y = sit(2, x)
// 
// if y > 0:
//     print("NO")
// else:
//     print("YES")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, values: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
