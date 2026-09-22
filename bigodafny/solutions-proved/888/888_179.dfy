// 1358_D. The Best Vacation  (problem 888, solution 888_179)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def sumprog(a, b):
//     return (a + b) * (b - a + 1) // 2
//  
//  
// n, x = map(int, input().split())
// d = list(map(int, input().split())) * 2
// max_hugs = 0
// i = 0
// j = 0
// days = 0
// hugs = 0
// while i < n:
//     if days + d[j] <= x:
//         days += d[j]
//         hugs += sumprog(1, d[j])
//         j += 1
//     else:
//         max_hugs = max(max_hugs, hugs + sumprog(d[j] - (x - days) + 1, d[j]))
//         hugs -= sumprog(1, d[i])
//         days -= d[i]
//         i += 1
// print(max_hugs)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Amortized two-pointer: each loop iteration advances exactly one of i, j by
// 1 (never both), i is capped at n and j at i+n (already in the row's own
// invariant), so total iterations <= n (from i) + 2n (from j's final value
// at i==n) = 3n. Charge each iteration O(1) and track steps against i+j.
method Solve(n: int, m: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires n == |a_list|
  requires n >= 1
  // The vacation fits inside one year, which is what bounds the window at n
  // months. A zero-length month only breaks that when the vacation is exactly
  // a year long, so the last clause rules out precisely that pairing -- 24
  // stored inputs contain a zero and the row's Python handles every one.
  requires forall k :: 0 <= k < |a_list| ==> a_list[k] >= 0
  requires m <= SumSeq(a_list)
  requires m < SumSeq(a_list) || forall k :: 0 <= k < |a_list| ==> a_list[k] >= 1
  ensures steps <= 7 * n + |output| + 10
{
  steps := 1;
  var d := a_list + a_list;
  steps := steps + n + 1;
  var max_hugs := 0;
  var i := 0;
  var j := 0;
  var days := 0;
  var hugs := 0;
  PrefixSumIsSumSeq(a_list);
  ghost var base1 := steps;
  while i < n
    invariant 0 <= i <= n
    // i can overtake j when a single month already exceeds x, so no i <= j here
    invariant 0 <= j <= i + n
    invariant |d| == 2 * n
    invariant days == PrefixSum(d, j) - PrefixSum(d, i)
    invariant steps <= base1 + 2 * (i + j)
    decreases n - i, |d| - j
  {
    PrefixSumWindowDoubled(a_list, i);
    assert j == i + n ==> days == PrefixSum(a_list, |a_list|);
    if days + d[j] <= m {
      assert j < i + n;
      days := days + d[j];
      hugs := hugs + SumProg(1, d[j]);
      j := j + 1;
    } else {
      var cand := hugs + SumProg(d[j] - (m - days) + 1, d[j]);
      if cand > max_hugs { max_hugs := cand; }
      hugs := hugs - SumProg(1, d[i]);
      days := days - d[i];
      i := i + 1;
    }
    steps := steps + 2;
  }
  assert i == n;
  assert j <= 2 * n;
  assert steps <= base1 + 2 * (n + 2 * n);
  output := IntToString(max_hugs) + "\n";
  steps := steps + |output| + 2;
}

function SumProg(a: int, b: int): int
{
  (a + b) * (b - a + 1) / 2
}
