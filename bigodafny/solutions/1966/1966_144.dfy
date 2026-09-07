// 25_B. Phone numbers  (problem 1966, solution 1966_144)
// time complexity: O(1)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// s = input()
// if n > 3:
//     if n % 2 == 0:
//         res = '-'.join(a + b for a, b in zip(s[::2], s[1::2]))
//     else:
//         res = s[0:3] + '-' + '-'.join(a + b for a, b in zip(s[3::2], s[4::2]))
//     print(res)
// else:
//     print(s)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, s: string) returns (output: string)
  requires |s| == n
{
  if n > 3 {
    var res: string;
    if n % 2 == 0 {
      var parts: seq<string> := [];
      var i := 0;
      while i + 1 < |s|
      {
        parts := parts + [s[i..i+2]];
        i := i + 2;
      }
      res := Join(parts, "-");
    } else {
      var parts: seq<string> := [];
      var i := 3;
      while i + 1 < |s|
      {
        parts := parts + [s[i..i+2]];
        i := i + 2;
      }
      res := s[0..3] + "-" + Join(parts, "-");
    }
    output := res + "\n";
  } else {
    output := s + "\n";
  }
}
