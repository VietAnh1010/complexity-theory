// 1351_B. Square?  (problem 1018, solution 1018_254)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// 
// for _ in range(int(input())):
//     a, b = map(int, input().split())
//     c, d = map(int, input().split())
//     if c + b == a == d or a + d == b == c or a + c == d == b or b + d == a == c:
//         print('Yes')
//     else:
//         print('No')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, edges: seq<seq<int>>) returns (output: string)
{
  var lines: seq<string> := [];
  var i := 0;
  while i < n
    decreases n - i
  {
    var a := edges[2 * i][0];
    var b := edges[2 * i][1];
    var c := edges[2 * i + 1][0];
    var d := edges[2 * i + 1][1];
    var flag := (c + b == a && a == d) || (a + d == b && b == c) || (a + c == d && d == b) || (b + d == a && a == c);
    lines := lines + [if flag then "Yes" else "No"];
    i := i + 1;
  }
  output := Join(lines, "\n");
}
