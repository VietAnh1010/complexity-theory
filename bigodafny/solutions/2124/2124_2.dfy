// 1077_A. Frog Jumping  (problem 2124, solution 2124_2)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t = int(input())
// answer = []
// for i in range(t):
//     a, b, k = map(int, input().split())
//     if k % 2 == 1:
//         answer.append(k // 2 * (a - b) + a)
//     else:
//         answer.append(k // 2 * (a - b))
// for i in range(t):
//     print(answer[i])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, queries: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
