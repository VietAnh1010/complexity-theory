// 1351_B. Square?  (problem 1018, solution 1018_254)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// 
// for _ in range(int(input())):
//     a, b = map(int, input().split())
//     c, d = map(int, input().split())
//     if c + b == a == d or a + d == b == c or a + c == d == b or b + d == a == c:
//         print('Yes')
//     else:
//         print('No')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, edges: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
