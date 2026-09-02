// 1256_C. Platforms Jumping  (problem 1748, solution 1748_21)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, m, d = list(map(int, input().strip().split(' ')))
// c = list(map(int, input().strip().split(' ')))
// 
// 
// res = []
// for i, ci in enumerate(c):
//     empty = n - len(res) - sum(c[i:])
//     if empty >= d - 1:
//         res.extend(['0']*(d - 1))
//     else:
//         res.extend(['0'] * empty)
//     res.extend([str(i + 1) for _ in range(ci)])
// 
// if n - len(res) < d:
//     res.extend(['0'] * (n - len(res)))
//     print("YES")
//     print(' '.join(res))
// else:
//     print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c: int, d_list: seq<int>) returns (output: string)
{
  var n := a;
  var m := b;
  var d := c;
  var res: seq<string> := [];
  var i := 0;
  while i < m
    decreases m - i
  {
    var ci := d_list[i];
    var suffix := SumSeq(d_list[i..]);
    var empty := n - |res| - suffix;
    var zeros := if empty >= d - 1 then d - 1 else empty;
    var z := 0;
    while z < zeros
      decreases zeros - z
    {
      res := res + ["0"];
      z := z + 1;
    }
    var k := 0;
    while k < ci
      decreases ci - k
    {
      res := res + [IntToString(i + 1)];
      k := k + 1;
    }
    i := i + 1;
  }
  if n - |res| < d {
    var pad := n - |res|;
    var p := 0;
    while p < pad
      decreases pad - p
    {
      res := res + ["0"];
      p := p + 1;
    }
    output := "YES\n" + Join(res, " ");
  } else {
    output := "NO";
  }
}
