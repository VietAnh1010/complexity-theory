// 1421_C. Palindromifier  (problem 450, solution 450_204)
// time complexity: O(1)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// print('3 L 2 R 2 R',len(input())*2-1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string) returns (output: string, ghost steps: nat)
  ensures steps <= 8
{
  steps := 1;
  // |s|, *2, -1: three constant-cost int ops. IntToString and its result
  // length are each charged 1. The two "+" concatenations each cost the
  // length of their right operand, which is 1 (IntToString's result) and
  // 1 ("\n") respectively.
  output := "3 L 2 R 2 R " + IntToString(|s| * 2 - 1) + "\n";
  steps := steps + 6;
}
