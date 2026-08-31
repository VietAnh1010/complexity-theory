// 608_A. Saitama Destroys Hotel  (problem 2425, solution 2425_188)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,s=map(int,input().split())
// f,t=map(int,input().split())
// p=max(s,f+t)
// for i in range(n-1):
//     f,t=map(int,input().split()) 
//     v=max(s,f+t)
//     if(p<v):
//         p=v
// print(p)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, pairs: seq<(int, int)>) returns (output: string)
{
  // Python takes max(s, f+t) pairwise and folds with max, which is just
  // max(s, max over pairs of f+t).
  var best := k;
  var i := 0;
  while i < |pairs|
    decreases |pairs| - i
  {
    var v := pairs[i].0 + pairs[i].1;
    if v > best { best := v; }
    i := i + 1;
  }
  output := IntToString(best) + "\n";
}
