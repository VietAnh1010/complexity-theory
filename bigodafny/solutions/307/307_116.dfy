// 729_A. Interview with Oleg  (problem 307, solution 307_116)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// s = input()
// p = "ogo"
// while len(p) < len(s):
// 	p += "go"
// while len(p) > 1:
// 	s = s.replace(p, "***")
// 	p = p[:-2]
// print(s) 
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, s: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
