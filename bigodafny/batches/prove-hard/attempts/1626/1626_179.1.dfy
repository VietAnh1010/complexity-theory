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

include "../../../../prelude.dfy"

ghost function Lg(k: int): nat
  decreases if k < 0 then 0 else k
{
  if k <= 0 then 0 else 1 + Lg(k / 2)
}

lemma LgMono(x: int, y: int)
  requires x <= y
  ensures Lg(x) <= Lg(y)
  decreases if y < 0 then 0 else y
{
  if x > 0 { LgMono(x / 2, y / 2); }
}

lemma LgStep(k: int, k2: int)
  requires k >= 1
  requires k2 <= k / 2
  ensures Lg(k2) + 1 <= Lg(k)
{
  LgMono(k2, k / 2);
}

ghost function SpanOf(l: seq<int>): int
  requires |l| > 0
{
  var s := Sort(l, (x: int, y: int) => x > y);
  SumSeq(s) - s[0]
}

method Solve(n: int, a_list: seq<int>)
    returns (output: string, ghost steps: nat)
  requires |a_list| == n
  requires n >= 1
  ensures steps <= 2 * NLogN(n) + n + 4 + Lg(SpanOf(a_list)) * (12 * n + 18) + |output|
{
  steps := 0;
  steps := steps + SortCost(|a_list|);
  var a := Sort(a_list, (x: int, y: int) => x > y);
  steps := steps + 1;
  var low := a[0];
  steps := steps + |a|;
  var high := SumSeq(a);
  SortCostWithin(|a_list|, n);
  ghost var base := steps;
  ghost var Kc: nat := 12 * n + 18;
  ghost var K0: int := SpanOf(a_list);
  ghost var it: nat := 0;
  assert base <= 2 * NLogN(n) + n + 2;
  assert K0 == high - low;
  while low < high
    invariant it + Lg(high - low) <= Lg(K0)
    invariant steps <= base + it * Kc
    decreases high - low
  {
    ghost var k := high - low;
    steps := steps + 2;
    steps := steps + 2;
    var mid := (low + high) / 2;
    var t := 0;
    var i := 0;
    var brk := false;
    ghost var s0 := steps;
    while i < n && t < mid && !brk
      invariant 0 <= i <= n
      invariant steps <= s0 + 12 * i + (if brk then 8 else 0)
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
    LgStep(k, high - low);
    CostMulDistrib(it, 1, it + 1, Kc);
    it := it + 1;
  }
  CostMulMonoLeft(it, Lg(K0), Kc);
  IntToStringDigits(high);
  steps := steps + 1;
  steps := steps + Digits(high);
  output := IntToString(high);
}

import opened Prelude
