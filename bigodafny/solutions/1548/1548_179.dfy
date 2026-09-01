// 1101_A. Minimum Integer  (problem 1548, solution 1548_179)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def minint(n, a):
//     for i in range(n):
//         l=a[i][0]
//         r=a[i][1]
//         d=a[i][2]
//         if  l<= d<=r:
//             print((r//d+1)*d)
//         else:
//             print(d)
// n=int(input())
// v=[]
// for i in range(n):
//     a = input().strip().split()
//     a = list(map(int, a))
//     v.append(a)
// minint(n, v)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, edges_list: seq<seq<int>>) returns (output: string)
{
  var lines: seq<string> := [];
  var i := 0;
  while i < n
    decreases n - i
  {
    var row := edges_list[i];
    var l := row[0];
    var r := row[1];
    var d := row[2];
    var line: string;
    if l <= d && d <= r {
      line := IntToString((FloorDiv(r, d) + 1) * d);
    } else {
      line := IntToString(d);
    }
    lines := lines + [line];
    i := i + 1;
  }
  output := Join(lines, "\n");
}
