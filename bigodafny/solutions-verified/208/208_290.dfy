// 554_A. Kyoya and Photobooks  (problem 208, solution 208_290)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// q=input()
// print((26*(len(q)+1))-len(q))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Label O(1) -- agrees, and this row is the control for the counting
// convention: `|s|` is a stored length, not a scan, so the whole method is
// straight-line work whose count does not mention the input at all.
method Solve(s: string) returns (output: string, ghost steps: nat)
  ensures steps <= 6
{
  output := IntToString(26 * (|s| + 1) - |s|) + "\n";
  steps := 6;
}
