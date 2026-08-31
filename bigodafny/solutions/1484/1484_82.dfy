// 172_A. Phone Code  (problem 1484, solution 1484_82)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// cases = int(input())
// 
// numbers = []
// while cases:
//     cases -= 1
//     s = input()
//     numbers.append(s)
// 
// numbers.sort()
// 
// ct = 0
// 
// for i, j in zip(numbers[0], numbers[-1]):
//     if i == j:
//         ct += 1
//     else:
//         print(ct)
//         break
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<string>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
