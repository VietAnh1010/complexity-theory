// 611_B. New Year and Old Property  (problem 1364, solution 1364_161)
// time complexity: O(logn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// ans = 0
// a, b = map(int, input().split())
// l = 2
// pos = l-2
// ans = 0
// while True:
//     n = ((1 << l) - 1) - (1 << pos)
//     #print(l, pos, n)
//     if n > b:
//         break
//     if n >= a:
//         ans += 1
//     if pos > 0:
//         pos -= 1
//     else:
//         l += 1
//         pos = l-2
// print(ans)
//     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
