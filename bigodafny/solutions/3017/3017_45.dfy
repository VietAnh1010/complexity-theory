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
  if |string_| == 0 {
    output := "";
    return;
  }
  var sorted := Sort(string_, (a: char, b: char) => a > b);
  var top := sorted[0];
  var i := 0;
  var result: seq<char> := [];
  while i < |sorted| && sorted[i] == top
    invariant 0 <= i <= |sorted|
    decreases |sorted| - i
  {
    result := result + [sorted[i]];
    i := i + 1;
  }
  output := result;
}
