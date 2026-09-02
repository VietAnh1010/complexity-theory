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

function ParseIntFrom(s: string, i: nat, acc: int): int
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i == |s| then acc
  else ParseIntFrom(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
}

function ParseInt(s: string): int
{
  if |s| > 0 && s[0] == '-' then -ParseIntFrom(s, 1, 0)
  else ParseIntFrom(s, 0, 0)
}

function ParseIntList(ss: seq<string>): seq<int>
  decreases |ss|
{
  if |ss| == 0 then [] else [ParseInt(ss[0])] + ParseIntList(ss[1..])
}


method Solve(n_str: string, a_list_str: string) returns (output: string)
{
  var n := ParseInt(n_str);
  var nums := ParseIntList(SplitWs(a_list_str));
  var INF := 1000000000;
  var firstPos := seq(n + 1, _ => INF);
  var lastPos := seq(n + 1, _ => -1);
  var i := 0;
  while i < |nums|
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
    decreases n - i
  {
    var first := firstPos[i];
    var lo := 0;
    var hi := |sortedLast|;
    while lo < hi
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
