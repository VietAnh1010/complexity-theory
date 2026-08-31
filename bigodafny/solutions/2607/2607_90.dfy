// 397_A. On Segment's Own Points  (problem 2607, solution 2607_90)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = [0] * 100
// la, ra = map(int, input().split())
// for i in range(1, n):
//     l, r = map(int, input().split())
//     a[l] += 1
//     if r < 100:
//         a[r] -= 1
// for i in range(1, 100):
//     a[i] += a[i - 1]
// ans = 0
// for i in range(la, ra):
//     if a[i] == 0:
//         ans += 1
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, intervals: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
