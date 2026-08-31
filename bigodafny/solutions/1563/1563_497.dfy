// 915_A. Garden  (problem 1563, solution 1563_497)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// buckets, length = map(int,input().split())
// data = list(map(int,input().split()))
// data.sort(reverse=True)
// for element in data:
//     if length % element == 0:
//         print(length // element)
//         break
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, values: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
