// 611_B. New Year and Old Property  (problem 1364, solution 1364_163)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def z(n):
//     n = bin(n)[2:]
//     k = len(n)
//     s = (k-1) * (k-2) // 2 + (n.count("0") == 1)
//     r = n.find("0")
//     s += k if r == -1 else r
// 
//     return s - 1;
// 
// a, b = map(int, input().split());
// print (z(b) - z(a - 1))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
