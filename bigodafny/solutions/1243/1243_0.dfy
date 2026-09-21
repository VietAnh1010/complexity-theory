// 186_A. Comparing Strings  (problem 1243, solution 1243_0)
// time complexity: O(nlogn+mlogm)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// g1=list(input())
// g2=list(input())
// cntr=0
// if sorted(g1)!=sorted(g2):
//     print('NO')
// else:
//     for i in range(len(g1)):
//         if g1[i]!=g2[i]:
//                 cntr=cntr+1
//     if cntr==2:
//         print('YES')
//     else:
//         print('NO')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// The equality test sorts, as the Python does. An earlier translation compared
// multisets instead: same answer on every test, one complexity class cheaper,
// and the O(nlogn+mlogm) label then described nothing in this file. Neither
// gate can see that -- both compare stdout -- so it took a proof to find it.
// Do not "simplify" this back to a multiset comparison.
method Solve(s1: string, s2: string) returns (output: string)
{
  var a := Sort(s1, (x: char, y: char) => x < y);
  var b := Sort(s2, (x: char, y: char) => x < y);
  if a != b {
    output := "NO";
  } else {
    assert |s1| == |a| == |b| == |s2|;
    var cntr := 0;
    var i := 0;
    while i < |s1|
      invariant 0 <= i <= |s1|
      decreases |s1| - i
    {
      if s1[i] != s2[i] { cntr := cntr + 1; }
      i := i + 1;
    }
    output := if cntr == 2 then "YES" else "NO";
  }
}
