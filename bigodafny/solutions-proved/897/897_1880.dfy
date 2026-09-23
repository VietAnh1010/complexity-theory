// 617_A. Elephant  (problem 897, solution 897_1880)
// time complexity: O(1)
// python exact-diff baseline: exact

include "../../prelude.dfy"
import opened Prelude

method Solve(number: int) returns (output: string, ghost steps: nat)
  ensures steps <= 6
{
  var ans := number / 5;
  var r := number % 5;
  if r != 0 { ans := ans + 1; }
  output := IntToString(ans) + "\n";
  steps := 6;
}
