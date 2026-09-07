// 416_A. Guess a number!  (problem 1878, solution 1878_29)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// u, v = -2000000000, 2000000000
// for i in range(int(input())):
//     a, b, c = input().split()
//     k = int(b)
//     if a == '>=':
//         if c == 'Y': u = max(u, k)
//         else: v = min(v, k - 1)
//     elif a == '>':
//         if c == 'Y': u = max(u, k + 1)
//         else: v = min(v, k)
//     elif a == '<=':
//         if c == 'Y': v = min(v, k)
//         else: u = max(u, k + 1)
//     else:
//         if c == 'Y': v = min(v, k - 1)
//         else: u = max(u, k)
// print('Impossible' if u > v else u)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(N: int, queries: seq<(string, int, string)>) returns (output: string)
  requires N >= 0
  requires |queries| >= N
{
  var u := -2000000000;
  var v := 2000000000;
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    decreases N - i
  {
    var a := queries[i].0;
    var k := queries[i].1;
    var c := queries[i].2;
    if a == ">=" {
      if c == "Y" { if k > u { u := k; } } else { if k - 1 < v { v := k - 1; } }
    } else if a == ">" {
      if c == "Y" { if k + 1 > u { u := k + 1; } } else { if k < v { v := k; } }
    } else if a == "<=" {
      if c == "Y" { if k < v { v := k; } } else { if k + 1 > u { u := k + 1; } }
    } else {
      if c == "Y" { if k - 1 < v { v := k - 1; } } else { if k > u { u := k; } }
    }
    i := i + 1;
  }
  output := if u > v then "Impossible" else IntToString(u);
}
