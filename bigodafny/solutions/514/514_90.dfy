// 913_C. Party Lemonade  (problem 514, solution 514_90)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def f(bs):
//     return int(bs, 2) // (1 << n - 1) * a[-1] + sum(a[i] for i in range(min(n - 1, len(bs))) if bs[-i - 1] == '1')
// n, x = map(int, input().split())
// *a, = map(int, input().split())
// for i in range(1, n):
//     a[i] = min(a[i], 2 * a[i - 1])
// bx = '0' * n + bin(x)[2:]
// ans = f(bx)
// for i in range(len(bx)):
//     if bx[i] == '0':
//         ans = min(ans, f(bx[:i] + '1' + '0' * (len(bx) - i - 1)))
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, total_score: int, scores: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
