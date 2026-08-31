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

method Solve(s: string) returns (output: string)
{
  output := IntToString(26 * (|s| + 1) - |s|) + "\n";
}
