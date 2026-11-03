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

include "../../prelude.dfy"
import opened Prelude

ghost function Rng(low: int, high: int): nat { if high > low then high - low else 0 }

ghost function Srt(a_list: seq<int>): seq<int> { Sort(a_list, (x: int, y: int) => x > y) }

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires |a_list| == n
  requires n >= 1
  ensures steps <= 2 * NLogN(n) + 5 * n + 20 + |output|
    + SearchPot(Rng(Srt(a_list)[0], SumSeq(Srt(a_list)))) * (8 * n + 12)
{
  steps := 1;
  var a := Sort(a_list, (x: int, y: int) => x > y);
  steps := steps + SortCost(n);
  SortCostWithin(n, n);
  assert a == Srt(a_list);
  var low := a[0];
  var high := SumSeq(a);
  steps := steps + n + 3;
  ghost var P := SearchPot(Rng(low, high));
  ghost var K := 8 * n + 12;
  ghost var it: nat := 0;
  ghost var b0 := steps;
  while low < high
    invariant it + SearchPot(Rng(low, high)) <= P
    invariant steps <= b0 + it * K
    decreases high - low
  {
    ghost var k := high - low;
    var mid := (low + high) / 2;
    var t := 0;
    var i := 0;
    var brk := false;
    steps := steps + 4;
    ghost var b1 := steps;
    while i < n && t < mid && !brk
      invariant 0 <= i <= n
      invariant steps <= b1 + 8 * i + (if brk then 8 else 0)
      decreases !brk, n - i
    {
      steps := steps + 8;
      if t >= a[i] {
        t := mid;
        brk := true;
      } else {
        t := t + (mid - a[i]);
        i := i + 1;
      }
    }
    if t >= mid {
      high := mid;
    } else {
      low := mid + 1;
    }
    BisectStep(k, Rng(low, high));
    CostMulDistrib(it, 1, it + 1, K);
    it := it + 1;
  }
  CostMulMonoLeft(it, P, K);
  output := IntToString(high);
  IntToStringDigits(high);
  steps := steps + |output| + 1;
}
