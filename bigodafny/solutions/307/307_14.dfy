// 729_A. Interview with Oleg  (problem 307, solution 307_14)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// s = input()
// for i in range(100, 0, -1):
//     s = s.replace('o' + 'go' * i, '***')
// print(s)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, s: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
