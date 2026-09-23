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

method Solve(n: int, matrix: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires forall k :: 0 <= k < |matrix| ==> |matrix[k]| >= 3
  ensures steps <= 19 * |matrix| + 3
{
  var lines: seq<string> := [];
  var t := 0;
  steps := 1;
  while t < |matrix|
    invariant 0 <= t <= |matrix|
    invariant |lines| == t
    invariant steps <= 18 * t + 1
    decreases |matrix| - t
  {
    var row := matrix[t];
    var a := row[0];
    var b := row[1];
    var c := row[2];
    steps := steps + 4;                 // row lookup + 3 elem reads
    var mi := MinSeq([a, b, c]) + 1;
    var ma := MaxSeq([a, b, c]) - 1;
    steps := steps + 3 + 3 + 2;         // two length-3 recursive scans + two +/- 1
    var ans := if ma - mi >= 0 then 2 * (ma - mi) else 0;
    steps := steps + 2;                 // compare + arithmetic
    lines := lines + [IntToString(ans)];
    steps := steps + 1 + 1;             // s + [x] charged 1, IntToString charged 1
    t := t + 1;
    steps := steps + 2;                 // increment + loop overhead
  }
  output := Join(lines, "\n");
  steps := steps + |lines| + 1;         // Join over |lines| digit-strings: exception, k not sum
}
