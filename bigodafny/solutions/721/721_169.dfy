// 1388_B. Captain Flint and a Long Voyage  (problem 721, solution 721_169)
// time complexity: O(n**2)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from math import ceil
// t = int(input())
// for _ in range(t):
//     n = int(input())
//     s = []
//     if n == 1:
//         print(8)
//     else:
//         s = ['9'] * (n - int(ceil(n / 4)))
//         s += ['8'] * int(ceil(n / 4))
//     print(''.join(s))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<int>) returns (output: string)
{
  var parts: seq<string> := [];
  var i := 0;
  while i < n && i < |numbers|
    invariant 0 <= i
    decreases n - i
  {
    var nv := numbers[i];
    if nv == 1 {
      parts := parts + ["8\n" + "\n"];
    } else if nv > 0 {
      var cnt8 := (nv + 3) / 4;
      var cnt9 := nv - cnt8;
      parts := parts + [Repeat("9", cnt9) + Repeat("8", cnt8) + "\n"];
    } else {
      parts := parts + ["\n"];
    }
    i := i + 1;
  }
  output := Join(parts, "");
}
