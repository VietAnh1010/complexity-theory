// 1400_A. String Similarity  (problem 2235, solution 2235_430)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #Written by Shagoto
// 
// t = int(input())
// for x in range(t):
//     n = int(input())
//     s = input()
//     
//     if(n == 1):
//         print(s)
//     
//     else:
//         for i in range(0, len(s), 2):
//             print(s[i], end = "")
//         print()
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(t: int, n_list: seq<int>, s_list: seq<string>) returns (output: string)
{
  var parts: seq<string> := [];
  var x := 0;
  while x < t
    decreases t - x
  {
    var n := n_list[x];
    var s := s_list[x];
    var line: string;
    if n == 1 {
      line := s;
    } else {
      var buf: string := "";
      var i := 0;
      while i < |s|
        decreases |s| - i
      {
        buf := buf + [s[i]];
        i := i + 2;
      }
      line := buf;
    }
    parts := parts + [line];
    x := x + 1;
  }
  output := Join(parts, "\n");
}
