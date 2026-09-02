// p02293 Parallel/Orthogonal  (problem 2183, solution 2183_2)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// q=int(input())
// 
// for _ in [0]*q:
//     x0,y0,x1,y1,x2,y2,x3,y3=map(int,input().split())
//     a1=x1-x0
//     a2=x3-x2
//     b1=y1-y0
//     b2=y3-y2
//     parallel=a1*b2-a2*b1
//     orthogonal=a1*a2+b1*b2
//     if parallel==0:
//         print("2")
//     elif orthogonal==0:
//         print("1")
//     else:
//         print("0")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, rows: seq<seq<int>>) returns (output: string)
{
  var lines: seq<string> := [];
  var i := 0;
  while i < n
    decreases n - i
  {
    var row := rows[i];
    var x0 := row[0]; var y0 := row[1]; var x1 := row[2]; var y1 := row[3];
    var x2 := row[4]; var y2 := row[5]; var x3 := row[6]; var y3 := row[7];
    var a1 := x1 - x0;
    var a2 := x3 - x2;
    var b1 := y1 - y0;
    var b2 := y3 - y2;
    var parallel := a1 * b2 - a2 * b1;
    var orthogonal := a1 * a2 + b1 * b2;
    var res := if parallel == 0 then 2 else if orthogonal == 0 then 1 else 0;
    lines := lines + [IntToString(res)];
    i := i + 1;
  }
  output := Join(lines, "\n");
}
