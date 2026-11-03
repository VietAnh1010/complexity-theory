// 348_A. Mafia  (problem 1626, solution 1626_179)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// 
// n = int(input())
// a = [int(x) for x in input().split()]
// a.sort(reverse=True)
// low = a[0]
// high = sum(a)
// while low < high:
// 	mid = (low + high) // 2
// 	t = 0
// 	i = 0
// 	while i < n and t < mid:
// 		if t >= a[i]:
// 			t = mid
// 			break
// 		t += (mid - a[i])
// 		i += 1
// 	if t >= mid:
// 		high = mid
// 	else:
// 		low = mid + 1
// print(high)
// --------------------------------------------------------------------

include "../../../prelude.dfy"

ghost function Rng(low: int, high: int): nat { if high > low then high - low else 0 }

ghost function Srt(a_list: seq<int>): seq<int> { Sort(a_list, (x: int, y: int) => x > y) }

method Solve(n: int, a_list: seq<int>)
    returns (output: string, ghost steps: nat)
  requires |a_list| == n
  requires n >= 1
  ensures steps <= 2 * NLogN(n) + 5 * n + 20 + |output|
    + SearchPot(Rng(Srt(a_list)[0], SumSeq(Srt(a_list)))) * (12 * n + 12)
{
  steps := 0;
  steps := steps + SortCost(|a_list|);
  var a := Sort(a_list, (x: int, y: int) => x > y);
  SortCostWithin(n, n);
  assert a == Srt(a_list);
  steps := steps + 1;
  var low := a[0];
  steps := steps + |a|;
  var high := SumSeq(a);
  ghost var P := SearchPot(Rng(low, high));
  ghost var K := 12 * n + 12;
  ghost var it: nat := 0;
  ghost var b0 := steps;
  while low < high
    invariant it + SearchPot(Rng(low, high)) <= P
    invariant steps <= b0 + it * K
    decreases high - low
  {
    ghost var k := high - low;
    steps := steps + 2;
    steps := steps + 2;
    var mid := (low + high) / 2;
    var t := 0;
    var i := 0;
    var brk := false;
    ghost var b1 := steps;
    while i < n && t < mid && !brk
      invariant 0 <= i <= n
      invariant brk ==> i < n
      invariant steps <= b1 + 12 * i + (if brk then 12 else 0)
      decreases !brk, n - i
    {
      steps := steps + (4 + (if i < n then 1 else 0) + if i < n && t < mid then 1 else 0);
      steps := steps + 2;
      if t >= a[i] {
        t := mid;
        brk := true;
      } else {
        steps := steps + 3;
        t := t + (mid - a[i]);
        steps := steps + 1;
        i := i + 1;
      }
    }
    steps := steps + (3 + (if i < n then 1 else 0) + if i < n && t < mid then 1 else 0);
    steps := steps + 1;
    if t >= mid {
      high := mid;
    } else {
      steps := steps + 1;
      low := mid + 1;
    }
    BisectStep(k, Rng(low, high));
    CostMulDistrib(it, 1, it + 1, K);
    it := it + 1;
  }
  CostMulMonoLeft(it, P, K);
  steps := steps + 1;
  IntToStringDigits(high);
  steps := steps + Digits(high);
  output := IntToString(high);
}

import opened Prelude
