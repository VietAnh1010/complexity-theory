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

function ReplaceAll(s: string, pat: string, rep: string): string
  requires |pat| > 0
  decreases |s|
{
  if |s| < |pat| then s
  else if s[0..|pat|] == pat then rep + ReplaceAll(s[|pat|..], pat, rep)
  else [s[0]] + ReplaceAll(s[1..], pat, rep)
}

// Replacing a pattern by something no longer than it never grows the string:
// the charge table's "recursive function over a string -> its length" line
// needs this to keep `cur`'s length bounded across the whole second loop.
lemma ReplaceAllLen(s: string, pat: string, rep: string)
  requires |pat| > 0 && |rep| <= |pat|
  ensures |ReplaceAll(s, pat, rep)| <= |s|
  decreases |s|
{
  if |s| < |pat| {
  } else if s[0..|pat|] == pat {
    ReplaceAllLen(s[|pat|..], pat, rep);
  } else {
    ReplaceAllLen(s[1..], pat, rep);
  }
}

method Solve(n: int, s: string) returns (output: string, ghost steps: nat)
  ensures steps <= (|s| + 1) + (|s| + 3) * (|s| + 5)
{
  steps := 1;
  var p := "ogo";
  while |p| < |s|
    invariant |p| <= |s| + 3
    invariant |p| % 2 == 1
    invariant steps <= |p| - 2
    decreases |s| - |p|
  {
    p := p + "go";
    steps := steps + 2;
  }
  // |p| is odd throughout, so once the second loop's guard |p| > 1 holds,
  // |p| >= 3 -- exactly what ReplaceAllLen needs against rep = "***".
  var cur := s;
  ghost var P0: nat := |p|;
  ghost var iters2: nat := 0;
  while |p| > 1
    invariant |cur| <= |s|
    invariant |p| % 2 == 1
    invariant 1 <= |p|
    invariant 2 * iters2 + |p| == P0
    invariant steps <= (|s| + 1) + iters2 * (|s| + 5)
    decreases |p|
  {
    ReplaceAllLen(cur, p, "***");
    cur := ReplaceAll(cur, p, "***");
    p := p[..|p| - 2];
    iters2 := iters2 + 1;
    steps := steps + |cur| + 2;
  }
  output := cur;
  // |p| == 1 here (odd and not > 1), so 2 * iters2 == P0 - 1 <= P0.
  assert iters2 <= 2 * iters2;
  assert 2 * iters2 <= P0;
  assert iters2 <= P0;
  assert P0 <= |s| + 3;
  CostMulMonoLeft(iters2, |s| + 3, |s| + 5);
}
