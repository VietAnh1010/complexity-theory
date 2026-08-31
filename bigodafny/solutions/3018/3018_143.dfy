// 299_A. Ksusha and Array  (problem 3018, solution 3018_143)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = list(map(int, input().split()))
// 
// a.sort()
// 
// t = a[0]
// for x in a:
//     if x % a[0] != 0:
//         t = -1
// 
// print(t)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
