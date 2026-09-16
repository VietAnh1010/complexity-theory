// p03072 AtCoder Beginner Contest 124 - Great Ocean View  (problem 1741, solution 1741_55)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// l=map(int,input().split())
// m=c=0
// for i in l:
//   if m<=i:
//     m=i
//     c+=1
// print(c)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, scores: seq<int>) returns (output: string)
{
  var m := 0;
  var c := 0;
  var i := 0;
  while i < |scores|
    decreases |scores| - i
  {
    if m <= scores[i] {
      m := scores[i];
      c := c + 1;
    }
    i := i + 1;
  }
  output := IntToString(c);
}
