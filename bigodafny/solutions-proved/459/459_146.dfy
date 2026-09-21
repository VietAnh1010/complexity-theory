// 519_C. A and B and Team Training  (problem 459, solution 459_146)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def maxTeams(a,b):
//     ans=min((a+b)//3,min(a,b))
//     return ans
//
// inputArray=input().strip().split()
// a=int(inputArray[0])
// b=int(inputArray[1])
// print(maxTeams(a,b))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string, ghost steps: nat)
  ensures steps <= 5
{
  steps := 1;
  var s := (a + b) / 3;
  steps := steps + 1;
  var mn := if a < b then a else b;
  steps := steps + 1;
  output := IntToString(if s < mn then s else mn);
  steps := steps + 2;
}
