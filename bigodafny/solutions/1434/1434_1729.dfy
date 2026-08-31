// 228_A. Is your horseshoe on the other hoof?  (problem 1434, solution 1434_1729)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// x = list(map(int, input().split()))
// dic ={}
// for each in x:
//     if each not in dic:
//         dic[each] = 0
//     dic[each] += 0
// h = len(dic)
// print(4 - h)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(values: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
