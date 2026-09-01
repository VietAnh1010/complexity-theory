// 1092_A. Uniform String  (problem 2254, solution 2254_143)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// for i in range(int(input())):
//     n,k=map(int,input().split())
//     s=""
//     x=0
//     for i in range(0,n):
//         s=s+chr(x+97)
//         x+=1
//         x=x%k
//     print(s)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs: seq<seq<int>>) returns (output: string)
{
  var parts: seq<string> := [];
  var t := 0;
  while t < n
    decreases n - t
  {
    var nn := pairs[t][0];
    var kk := pairs[t][1];
    var s: string := "";
    var x := 0;
    var i := 0;
    while i < nn
      decreases nn - i
    {
      s := s + [((x + 97) as char)];
      x := x + 1;
      x := x % kk;
      i := i + 1;
    }
    parts := parts + [s];
    t := t + 1;
  }
  output := Join(parts, "\n");
}
