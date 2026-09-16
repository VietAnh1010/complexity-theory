// 1251_A. Broken Keyboard  (problem 960, solution 960_36)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t = int(input())
// for _ in range(t):
//     s = list(input().strip())
//     g = set()
//     n = len(s)
//     c = 1
//     if n==1:
//         print(s[0])
//     else:
//         for i in range(1,n):
//             if s[i]!=s[i-1] and c&1:
//                 g.add(s[i-1])
//             else:
//                 c += 1
//             if i==n-1 and c&1:
//                 g.add(s[i])
//         print(''.join(sorted(list(g))))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, strings: seq<string>) returns (output: string)
{
  var lines: seq<string> := [];
  var si := 0;
  while si < |strings|
    decreases |strings| - si
  {
    var s := strings[si];
    var m := |s|;
    var lineOut: string;
    if m == 1 {
      lineOut := [s[0]];
    } else {
      var g: set<char> := {};
      var c := 1;
      var i := 1;
      while i < m
        decreases m - i
      {
        if s[i] != s[i-1] && c % 2 == 1 {
          g := g + {s[i-1]};
        } else {
          c := c + 1;
        }
        if i == m-1 && c % 2 == 1 {
          g := g + {s[i]};
        }
        i := i + 1;
      }
      var elems: seq<char> := [];
      var gg := g;
      while gg != {}
        decreases |gg|
      {
        var x :| x in gg;
        elems := elems + [x];
        gg := gg - {x};
      }
      lineOut := Sort(elems, (a, b) => a < b);
    }
    lines := lines + [lineOut];
    si := si + 1;
  }
  output := Join(lines, "\n");
}
