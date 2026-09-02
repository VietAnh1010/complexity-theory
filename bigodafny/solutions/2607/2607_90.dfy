// 397_A. On Segment's Own Points  (problem 2607, solution 2607_90)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = [0] * 100
// la, ra = map(int, input().split())
// for i in range(1, n):
//     l, r = map(int, input().split())
//     a[l] += 1
//     if r < 100:
//         a[r] -= 1
// for i in range(1, 100):
//     a[i] += a[i - 1]
// ans = 0
// for i in range(la, ra):
//     if a[i] == 0:
//         ans += 1
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, intervals: seq<seq<int>>) returns (output: string)
  requires n == |intervals|
  requires forall k :: 0 <= k < |intervals| ==> |intervals[k]| >= 2
  requires n >= 1
{
  var a := seq(100, _ => 0);
  var la := intervals[0][0];
  var ra := intervals[0][1];
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant |a| == 100
    decreases n - i
  {
    var l := intervals[i][0];
    var r := intervals[i][1];
    if 0 <= l < 100 {
      a := a[l := a[l] + 1];
    }
    if 0 <= r < 100 {
      a := a[r := a[r] - 1];
    }
    i := i + 1;
  }
  i := 1;
  while i < 100
    invariant 1 <= i <= 100
    invariant |a| == 100
    decreases 100 - i
  {
    a := a[i := a[i] + a[i - 1]];
    i := i + 1;
  }
  var ans := 0;
  var t := la;
  while t < ra
    invariant |a| == 100
    decreases ra - t
  {
    if 0 <= t < 100 && a[t] == 0 {
      ans := ans + 1;
    }
    t := t + 1;
  }
  output := IntToString(ans);
}
