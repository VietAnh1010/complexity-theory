// 554_A. Kyoya and Photobooks  (problem 208, solution 208_189)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s = input()
// d = set()
// for i in range(len(s)):
//     for a in range(26):
//         c = chr(ord('a') + a)
//         d.add(s[:i] + c + s[i:])
// for a in range(26):
//         c = chr(ord('a') + a)
//         d.add(s + c)
// print(len(d))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string) returns (output: string)
{
  var d: set<string> := {};
  var i := 0;
  while i < |s|
    decreases |s| - i
  {
    var a := 0;
    while a < 26
      decreases 26 - a
    {
      var ch := ((('a' as int) + a) as char);
      d := d + {s[..i] + [ch] + s[i..]};
      a := a + 1;
    }
    i := i + 1;
  }
  var a2 := 0;
  while a2 < 26
    decreases 26 - a2
  {
    var ch := ((('a' as int) + a2) as char);
    d := d + {s + [ch]};
    a2 := a2 + 1;
  }
  output := IntToString(|d|);
}
