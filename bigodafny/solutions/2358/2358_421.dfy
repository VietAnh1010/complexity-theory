// 914_A. Perfect Squares  (problem 2358, solution 2358_421)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// input()
// ar = list(map(int, input().split()))
// 
// maxim = -10 ** 6
// 
// for i in ar:
//     if (i < 0 or (int(i ** 0.5)) ** 2 != i) and i > maxim:
//         maxim = i
// 
// print(maxim)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
