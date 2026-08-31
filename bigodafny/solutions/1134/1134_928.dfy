// 1272_A. Three Friends  (problem 1134, solution 1134_928)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// rr = lambda: input().strip()
// rri = lambda: int(rr())
// rrm = lambda: map(int, rr().split())
// 
// def solve(a,b,c):
//     mi = min(a,b,c)
//     mi += 1
//     ma = max(a,b,c)
//     ma -= 1
//     if(ma-mi>=0):
//         return 2*(ma-mi)
//     else:
//         return 0 
// 
// T = rri()
// for i in range(T):
//     a,b,c = rrm()
//     ans = solve(a,b,c)
//     print(ans) 
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, matrix: seq<seq<int>>) returns (output: string)
{
  var lines: seq<string> := [];
  var t := 0;
  while t < |matrix|
    decreases |matrix| - t
  {
    var row := matrix[t];
    var a := row[0];
    var b := row[1];
    var c := row[2];
    var mi := MinSeq([a, b, c]) + 1;
    var ma := MaxSeq([a, b, c]) - 1;
    var ans := if ma - mi >= 0 then 2 * (ma - mi) else 0;
    lines := lines + [IntToString(ans)];
    t := t + 1;
  }
  output := Join(lines, "\n");
}

