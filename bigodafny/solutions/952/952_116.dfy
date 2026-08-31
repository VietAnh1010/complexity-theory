// 977_F. Consecutive Subsequence  (problem 952, solution 952_116)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = list(map(int, input().split()))
// dc = dict()
// for x in a:
//     dc[x] = max(dc.get(x, 0), dc.get(x - 1, 0) + 1)
// ans = 0
// mx = 0
// for x in dc.keys():
//     if dc[x] > mx:
//         mx = dc[x]
//         ans = x
// arr = []
// for i in range(n - 1, -1, -1):
//     if a[i] == ans:
//         ans -= 1
//         arr.append(i + 1)
// print(len(arr))
// print(*arr[::-1])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
