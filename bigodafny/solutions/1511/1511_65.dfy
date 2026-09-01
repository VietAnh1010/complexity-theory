// 385_B. Bear and Strings  (problem 1511, solution 1511_65)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def f(s):
//     n  = len(s)
//     c  = 0
//     ll = 0
//     for i in range(n-3):
//         if s[i:i+4] == 'bear':
//             l  = i-ll+1
//             r  = n-i-3
//             c += l*r
//             ll = i+1
//     return c
// 
// s = input()
// print(f(s))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(string_: string) returns (output: string)
{
  var s := string_;
  var n := |s|;
  var c := 0;
  var ll := 0;
  var i := 0;
  while i < n - 3
    decreases n - 3 - i
  {
    if s[i..i+4] == "bear" {
      var l := i - ll + 1;
      var r := n - i - 3;
      c := c + l * r;
      ll := i + 1;
    }
    i := i + 1;
  }
  output := IntToString(c);
}
