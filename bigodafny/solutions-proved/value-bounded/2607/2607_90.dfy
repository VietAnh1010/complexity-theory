// VALUE-BOUNDED -- filed for review; the proof carries a term the label omits.
//
//   This proof's bound depends on the MAGNITUDE of an input, not only on how
//   many inputs there are. BigOBench fitted the label by profiling, which
//   treats a capped value as constant; COMPLEXITY.md section 1 decides the
//   opposite, so the two disagree here by construction.
//
//   See solutions-proved/value-bounded/README.md for the category and
//   MANIFEST.jsonl for this row's entry.
//
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

include "../../../prelude.dfy"
import opened Prelude

// The third loop runs from la to ra -- values read straight out of
// intervals[0], with no `requires` bounding them (the original Python has no
// such bound either; it would IndexError past 100, which the array-bound
// checks below only guard against, not prevent from iterating). So the
// proved bound below is honest but NOT pure O(n): it carries a second,
// separate term in (ra - la) that no requires in this file ties to n.
method Solve(n: int, intervals: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires n == |intervals|
  requires forall k :: 0 <= k < |intervals| ==> |intervals[k]| >= 2
  requires n >= 1
  ensures steps <= 6 * n + 400 +
    4 * (if intervals[0][1] > intervals[0][0] then intervals[0][1] - intervals[0][0] else 0)
{
  steps := 1;
  var a := seq(100, _ => 0);
  var la := intervals[0][0];
  var ra := intervals[0][1];
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant |a| == 100
    invariant steps == 6 * i - 5
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
    steps := steps + 6;
  }
  assert steps <= 6 * n - 5;
  i := 1;
  while i < 100
    invariant 1 <= i <= 100
    invariant |a| == 100
    invariant steps <= 6 * n - 5 + 3 * (i - 1)
    decreases 100 - i
  {
    a := a[i := a[i] + a[i - 1]];
    i := i + 1;
    steps := steps + 3;
  }
  assert steps <= 6 * n - 5 + 3 * 99;
  var ans := 0;
  var t := la;
  while t < ra
    invariant |a| == 100
    invariant t >= la
    invariant t <= (if ra >= la then ra else la)
    invariant steps <= 6 * n - 5 + 3 * 99 + 4 * (if t > la then t - la else 0)
    decreases ra - t
  {
    if 0 <= t < 100 && a[t] == 0 {
      ans := ans + 1;
    }
    t := t + 1;
    steps := steps + 4;
  }
  output := IntToString(ans);
  steps := steps + 1;
  if ra > la {
    assert t == ra;
    assert steps <= 6 * n - 5 + 3 * 99 + 4 * (ra - la) + 1;
  } else {
    assert t == la;
    assert steps <= 6 * n - 5 + 3 * 99 + 1;
  }
  assert steps <= 6 * n - 5 + 3 * 99 + 4 * (if ra > la then ra - la else 0) + 1;
}
