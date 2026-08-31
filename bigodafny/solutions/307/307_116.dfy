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
  var p := "ogo";
  while |p| < |s|
    decreases |s| - |p|
  {
    p := p + "go";
  }
  var cur := s;
  while |p| > 1
    decreases |p|
  {
    cur := ReplaceAll(cur, p, "***");
    p := p[..|p| - 2];
  }
  output := cur;
}

function ReplaceAll(s: string, pat: string, rep: string): string
  requires |pat| > 0
  decreases |s|
{
  if |s| < |pat| then s
  else if s[0..|pat|] == pat then rep + ReplaceAll(s[|pat|..], pat, rep)
  else [s[0]] + ReplaceAll(s[1..], pat, rep)
}
