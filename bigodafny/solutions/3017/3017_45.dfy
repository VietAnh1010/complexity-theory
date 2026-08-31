// 202_A. LLPS  (problem 3017, solution 3017_45)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def solution(l1):
//     l1.sort()
//     l1.reverse()
//     c_out=""
//     for x in l1:
//         if x==l1[0]:
//             c_out+=x
//     return c_out
// def answer():
//     l1 = list(input())
//     print(solution(l1))
// answer()
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(string_: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
