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

include "../../prelude.dfy"
import opened Prelude


method Solve(n_str: string, a_list_str: string) returns (output: string)
  requires ParseInt(n_str) >= 0
  requires |ParseInts(SplitWs(a_list_str))| == ParseInt(n_str)
  requires forall k :: 0 <= k < |ParseInts(SplitWs(a_list_str))| ==>
             1 <= ParseInts(SplitWs(a_list_str))[k] <= ParseInt(n_str)
{
  var n := ParseInt(n_str);
  var nums := ParseInts(SplitWs(a_list_str));
  var INF := 1000000000;
  var firstPos := seq(n + 1, _ => INF);
  var lastPos := seq(n + 1, _ => -1);
  var i := 0;
  while i < |nums|
    invariant 0 <= i <= |nums|
    invariant |firstPos| == n + 1
    decreases |nums| - i
  {
    var x := nums[i];
    if firstPos[x] == INF {
      firstPos := firstPos[x := i];
    }
    i := i + 1;
  }
  i := 0;
  while i < |nums|
    invariant 0 <= i <= |nums|
    invariant |lastPos| == n + 1
    decreases |nums| - i
  {
    var x := nums[i];
    lastPos := lastPos[x := i];
    i := i + 1;
  }
  var sortedLast := SortInts(lastPos);
  var total := 0;
  i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant |firstPos| == n + 1
    decreases n - i
  {
    var first := firstPos[i];
    var lo := 0;
    var hi := |sortedLast|;
    while lo < hi
      invariant 0 <= lo <= hi <= |sortedLast|
      decreases hi - lo
    {
      var mid := (lo + hi) / 2;
      if sortedLast[mid] <= first {
        lo := mid + 1;
      } else {
        hi := mid;
      }
    }
    total := total + (|sortedLast| - lo);
    i := i + 1;
  }
  output := IntToString(total);
}
