// 1400_A. String Similarity  (problem 2235, solution 2235_384)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #872
// for _ in range(int(input())):
//     n=int(input())
//     a=input()
//     print(a[::2])
//         
//     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(t: int, n_list: seq<int>, s_list: seq<string>) returns (output: string)
{
  var lines: seq<string> := [];
  var i := 0;
  while i < t
    decreases t - i
  {
    var s := s_list[i];
    var res: seq<char> := [];
    var j := 0;
    while j < |s|
      decreases |s| - j
    {
      if j % 2 == 0 { res := res + [s[j]]; }
      j := j + 1;
    }
    lines := lines + [res];
    i := i + 1;
  }
  output := Join(lines, "\n");
}
