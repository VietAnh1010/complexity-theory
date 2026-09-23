// 667_B. Coat of Anticubism  (problem 2071, solution 2071_39)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = list(map(int, input().split()))
// s = sum(a)
// t = 0
// a.sort(reverse = True)
// for i in a :
//     t += i
//     s -= i
//     if(t >= s) :
//         break
// 
// print(t - s + 1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Sort's own cost via the standard T(k) = T(k/2) + T(k-k/2) + k recurrence,
// bounded O(k log k) -- precedent solutions-proved/1871/1871_156.dfy.
// SumSeq is a recursive prelude function over a_list: charged its length.
// The scan loop is linear and dominated by the sort.

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * |a_list| * (CeilLog2(|a_list|) + 1) + 6 * |a_list| + |output| + 10
{
  var a := Sort(a_list, (x: int, y: int) => x > y);
  SortCostTreeBound(|a_list|);
  steps := 1 + SortCost(|a_list|);
  var s := SumSeq(a_list);
  steps := steps + |a_list| + 1;
  var t := 0;
  var idx := 0;
  var stopped := false;
  ghost var base1 := steps;
  while idx < |a| && !stopped
    invariant 0 <= idx <= |a|
    invariant steps <= base1 + 3 * idx
    decreases |a| - idx
  {
    var i := a[idx];
    t := t + i;
    s := s - i;
    if t >= s {
      stopped := true;
    }
    idx := idx + 1;
    steps := steps + 3;
  }
  assert |a| == |a_list|;
  assert steps <= base1 + 3 * |a_list|;
  output := IntToString(t - s + 1);
  steps := steps + |output| + 2;
}
