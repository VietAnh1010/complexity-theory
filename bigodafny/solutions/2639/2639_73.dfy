// 975_B. Mancala  (problem 2639, solution 2639_73)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a = list(map(int, input().split()))
// 
// ans = 0
// for i in range(len(a)):
//     x = a[i]
//     b = [j for j in a]
//     b[i] = 0
//     for j in range(len(a)):
//         b[j] += x // 14
//     
//     for j in range(1, x % 14 + 1):
//         b[(i + j) % 14] += 1
//         
//     ans_now = 0
//     for j in b:
//         if j % 2 == 0:
//             ans_now += j
//     ans = max(ans_now, ans)
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(values: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
