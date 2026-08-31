// 442_B. Andrey and Problem  (problem 2496, solution 2496_30)
// time complexity: O(nlogn)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// 
// input()
// ps = sorted((float(p) for p in input().split()), reverse=True)
// if 1.0 in ps:
//     print(1)
//     sys.exit()
// a, b = 0, 1
// for p in ps:
//     c, d = a + p / (1 - p), b * (1 - p)
//     if c * d > a * b:
//         a, b = c, d
//     else:
//         break
// print('{:.9}'.format(a * b))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<real>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
