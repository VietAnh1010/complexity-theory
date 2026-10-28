// 1004_C. Sonya and Robots  (problem 1039, solution 1039_15)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
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

// PROOF NOTE (relation: confirms).
// Two O(n) passes, a sort of the n + 1 last positions, then for each of the
// n + 1 first positions a binary search over the sorted list. The searches are
// bounded by the prelude's SearchPot potential and folded, together with the
// sort, into NLogN(n + 1) by SearchLoopWithin and SortCostNLogN. Reading the
// input is charged the length of the strings read.

include "../../prelude.dfy"
import opened Prelude


method {:isolate_assertions} Solve(n_str: string, a_list_str: string) returns (output: string, ghost steps: nat)
  requires ParseInt(n_str) >= 0
  requires |ParseInts(SplitWs(a_list_str))| == ParseInt(n_str)
  requires forall k :: 0 <= k < |ParseInts(SplitWs(a_list_str))| ==>
             1 <= ParseInts(SplitWs(a_list_str))[k] <= ParseInt(n_str)
  ensures steps <= 5 * NLogN(ParseInt(n_str) + 1) + 11 * ParseInt(n_str) + |n_str| + |a_list_str| + |output| + 10
{
  var n := ParseInt(n_str);
  var nums := ParseInts(SplitWs(a_list_str));
  // reading the input: each parse is linear in the string it reads
  steps := 1 + |n_str| + |a_list_str|;
  ghost var N: nat := n + 1;
  var INF := 1000000000;
  var firstPos := seq(n + 1, _ => INF);
  var lastPos := seq(n + 1, _ => -1);
  steps := steps + 2 * N;
  var i := 0;
  while i < |nums|
    invariant 0 <= i <= |nums|
    invariant |firstPos| == n + 1
    invariant steps == 1 + |n_str| + |a_list_str| + 2 * N + 3 * i
    decreases |nums| - i
  {
    var x := nums[i];
    if firstPos[x] == INF {
      firstPos := firstPos[x := i];
    }
    i := i + 1;
    steps := steps + 3;
  }
  i := 0;
  while i < |nums|
    invariant 0 <= i <= |nums|
    invariant |lastPos| == n + 1
    invariant steps == 1 + |n_str| + |a_list_str| + 2 * N + 3 * n + 2 * i
    decreases |nums| - i
  {
    var x := nums[i];
    lastPos := lastPos[x := i];
    i := i + 1;
    steps := steps + 2;
  }
  var sortedLast := SortInts(lastPos);
  steps := steps + SortCost(N);
  SortCostNLogN(N);
  ghost var base := steps;
  ghost var K: nat := 3 * SearchPot(N) + 4;
  var total := 0;
  i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant |firstPos| == n + 1
    invariant |sortedLast| == N
    invariant steps <= base + i * K
    decreases n - i
  {
    var first := firstPos[i];
    var lo := 0;
    var hi := |sortedLast|;
    ghost var it: nat := 0;
    ghost var s0 := steps;
    while lo < hi
      invariant 0 <= lo <= hi <= |sortedLast|
      invariant it + SearchPot(hi - lo) <= SearchPot(N)
      invariant steps == s0 + 3 * it
      decreases hi - lo
    {
      var mid := (lo + hi) / 2;
      ghost var k := hi - lo;
      if sortedLast[mid] <= first {
        lo := mid + 1;
      } else {
        hi := mid;
      }
      BisectStep(k, hi - lo);
      it := it + 1;
      steps := steps + 3;
    }
    total := total + (|sortedLast| - lo);
    i := i + 1;
    steps := steps + 4;
    assert steps <= s0 + 3 * SearchPot(N) + 4;
    CostMulDistrib(i - 1, 1, i, K);
  }
  assert i == N;
  SearchLoopWithin(N, N, N, 3, 4);
  assert steps <= base + 3 * NLogN(N) + 4 * N;
  output := IntToString(total);
  IntToStringDigits(total);
  steps := steps + 1 + |output|;
}
