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

method Solve(string_: string) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * NLogN(|string_|) + 5 * |string_| + 5
{
  steps := 1;
  if |string_| == 0 {
    output := "";
    return;
  }
  var sorted := Sort(string_, (a: char, b: char) => a > b);
  steps := steps + SortCost(|string_|);
  SortCostWithin(|string_|, |string_|);
  var top := sorted[0];
  steps := steps + 1;
  var i := 0;
  var result: seq<char> := [];
  while i < |sorted| && sorted[i] == top
    invariant 0 <= i <= |sorted|
    invariant steps <= 2 * NLogN(|string_|) + 3 * i + 4
    decreases |sorted| - i
  {
    result := result + [sorted[i]];
    i := i + 1;
    steps := steps + 3;
  }
  output := result;
  steps := steps + 1;
}
