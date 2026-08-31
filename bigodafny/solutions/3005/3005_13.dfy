// p02417 Counting Characters  (problem 3005, solution 3005_13)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// s=sys.stdin.read().lower()
// a=[print(i,':',s.count(i)) for i in map(chr,range(97,123))]
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(text: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
