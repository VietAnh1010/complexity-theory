// 137_B. Permutation  (problem 1413, solution 1413_222)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// x = list(map(int, input().split()))
// a, list_of_set = n * [0], n * [0]
// ans = 0
// for i in range(1, n + 1):
//     a[i - 1] = i
// for j in range(n):
//     if j + 1 in set(x):
//         list_of_set[j] = j + 1
// for k in range(n):
//     if list_of_set[k] != a[k]:
//         ans += 1
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, values: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
