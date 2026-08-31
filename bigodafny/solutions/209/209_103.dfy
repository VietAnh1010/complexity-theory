// 624_B. Making a String  (problem 209, solution 209_103)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = list(sorted(map(int, input().split()), reverse=True))
// for i in range(n - 1):
//     a[i + 1] = max(0, min(a[i] - 1, a[i + 1]))
// print(sum(a))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(N: int, numbers: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
