// 630_H. Benches  (problem 2803, solution 2803_133)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def fact(i):
//   ans = 1
//   for j in range(1, i + 1):
//     ans *= j
//   return ans
// 
// def c(i, j):
//   return fact(i) // (fact(j) * fact(i - j))
// 
// n = int(input())
// ans = 1
// for j in range(5):
//  ans *= n - j
// print(ans * c(n, 5))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
