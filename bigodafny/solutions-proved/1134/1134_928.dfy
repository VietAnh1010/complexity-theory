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

lemma SumLenAppend(a: seq<string>, x: string)
  ensures SumLen(a + [x]) == SumLen(a) + |x|
  decreases |a|
{
  if |a| > 0 {
    assert (a + [x])[1..] == a[1..] + [x];
    SumLenAppend(a[1..], x);
  }
}

method Solve(n: int, matrix: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires forall k :: 0 <= k < |matrix| ==> |matrix[k]| >= 3
  ensures steps <= 11 * |matrix| + 2 + 2 * |output|
{
  steps := 1;
  var lines: seq<string> := [];
  var t := 0;
  while t < |matrix|
    invariant 0 <= t <= |matrix|
    invariant |lines| == t
    invariant steps <= 10 * t + 1 + SumLen(lines)
    decreases |matrix| - t
  {
    var row := matrix[t];
    var a := row[0];
    var b := row[1];
    var c := row[2];
    var mi := MinSeq([a, b, c]) + 1;
    var ma := MaxSeq([a, b, c]) - 1;
    var ans := if ma - mi >= 0 then 2 * (ma - mi) else 0;
    IntToStringDigits(ans);
    SumLenAppend(lines, IntToString(ans));
    lines := lines + [IntToString(ans)];
    t := t + 1;
    steps := steps + 10 + Digits(ans);
  }
  output := Join(lines, "\n");
  if |lines| >= 1 { JoinLen(lines, "\n"); }
  steps := steps + SumLen(lines) + |lines| + 1;
}
