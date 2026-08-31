// 889_A. Petya and Catacombs  (problem 1367, solution 1367_59)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = list(map(int, input().split()))
// di = {0 : 0}
// k = 1
// q = 1
// for i in a:
//     if i in di:
//         del di[i]
//     else:
//         q += 1
//     di[k] = i
//     k += 1
// print(q)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, coordinates: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
