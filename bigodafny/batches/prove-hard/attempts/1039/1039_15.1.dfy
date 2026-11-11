// --- Python ---------------------------------------------------------
// from collections import defaultdict
// from bisect import bisect
// 
// INF = 10**9
// 
// n = int(input())
// a = list(map(int, input().split()))
// 
// first_pos = [INF] * (n+1)
// for i, x in enumerate(a):
//     if first_pos[x] == INF:
//         first_pos[x] = i
//         
// last_pos = [-1] * (n+1)
// for i, x in enumerate(a):
//     last_pos[x] = i
// last_pos.sort()
// 
// total = 0
// for i, first in enumerate(first_pos):
//     total += len(last_pos) - bisect(last_pos, first)
// print(total)
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

method Solve(n_str: string, a_list_str: string)
    returns (output: string, ghost steps: nat)
  requires ParseInt(n_str) >= 0
  requires |ParseInts(SplitWs(a_list_str))| == ParseInt(n_str)
  requires forall k :: 0 <= k < |ParseInts(SplitWs(a_list_str))| ==> 1 <= ParseInts(SplitWs(a_list_str))[k] <= ParseInt(n_str)
  ensures steps <= |n_str| + |a_list_str| + SumLen(SplitWs(a_list_str)) + 9 * NLogN(ParseInt(n_str) + 1) + 30 * ParseInt(n_str) + 30 + |output|
{
  steps := 0;
  steps := steps + |n_str|;
  var n := ParseInt(n_str);
  steps := steps + (|a_list_str| + SumLen(SplitWs(a_list_str)));
  var nums := ParseInts(SplitWs(a_list_str));
  var INF := 1000000000;
  steps := steps + (1 + (n + 1));
  var firstPos := seq(n + 1, _ /* _v0 */ => INF);
  steps := steps + (1 + (n + 1));
  var lastPos := seq(n + 1, _ /* _v1 */ => -1);
  var i := 0;
  assert |nums| == n;
  ghost var a1 := steps;
  while i < |nums|
    invariant 0 <= i <= |nums|
    invariant |firstPos| == n + 1
    invariant steps <= a1 + 8 * i
    decreases |nums| - i
  {
    steps := steps + 3;
    steps := steps + 1;
    var x := nums[i];
    steps := steps + 2;
    if firstPos[x] == INF {
      steps := steps + 1;
      firstPos := firstPos[x := i];
    }
    steps := steps + 1;
    i := i + 1;
  }
  steps := steps + 2;
  i := 0;
  ghost var a2 := steps;
  while i < |nums|
    invariant 0 <= i <= |nums|
    invariant |lastPos| == n + 1
    invariant steps <= a2 + 6 * i
    decreases |nums| - i
  {
    steps := steps + 3;
    steps := steps + 1;
    var x := nums[i];
    steps := steps + 1;
    lastPos := lastPos[x := i];
    steps := steps + 1;
    i := i + 1;
  }
  steps := steps + 2;
  steps := steps + SortCost(|lastPos|);
  var sortedLast := SortInts(lastPos);
  SortCostWithin(|lastPos|, n + 1);
  var total := 0;
  i := 0;
  ghost var P := SearchPot(n + 1);
  ghost var K := 7 * P + 9;
  ghost var base := steps;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant |firstPos| == n + 1
    invariant |sortedLast| == n + 1
    invariant steps <= base + i * K
    decreases n - i
  {
    steps := steps + 2;
    steps := steps + 1;
    var first := firstPos[i];
    var lo := 0;
    steps := steps + 1;
    var hi := |sortedLast|;
    ghost var s0 := steps;
    ghost var it: nat := 0;
    while lo < hi
      invariant 0 <= lo <= hi <= |sortedLast|
      invariant it + SearchPot(hi - lo) <= SearchPot(n + 1)
      invariant steps <= s0 + 7 * it
      decreases hi - lo
    {
      ghost var k := hi - lo;
      steps := steps + 2;
      steps := steps + 2;
      var mid := (lo + hi) / 2;
      steps := steps + 2;
      if sortedLast[mid] <= first {
        steps := steps + 1;
        lo := mid + 1;
      } else {
        hi := mid;
      }
      BisectStep(k, hi - lo);
      it := it + 1;
    }
    steps := steps + 1;
    steps := steps + 3;
    total := total + (|sortedLast| - lo);
    steps := steps + 1;
    i := i + 1;
    CostMulDistrib(i - 1, 1, i, K);
  }
  steps := steps + 1;
  steps := steps + Digits(total);
  output := IntToString(total);
  IntToStringDigits(total);
  SearchLoopWithin(n + 1, n + 1, n + 1, 7, 9);
  CostMulDistrib(n + 1, 0, n + 1, K);
}

import opened Prelude
