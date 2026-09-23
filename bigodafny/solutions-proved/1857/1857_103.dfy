// 903_C. Boxes Packing  (problem 1857, solution 1857_103)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// a=sorted(list(map(int,input().split())))
// d={}
// for i in a:
//     if i not in d:
//         d[i]=1
//     else:
//         d[i]+=1
// print(max(d.values()))
//
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * |a_list| * (CeilLog2(|a_list|) + 1) + 5 * |a_list| + 6
{
  var sorted := SortInts(a_list);
  SortCostTreeBound(|a_list|);
  var maxCount := 0;
  var i := 0;
  steps := 1 + SortCost(|a_list|);
  ghost var base1 := steps;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    invariant steps <= base1 + 5 * i
    decreases |sorted| - i
  {
    var j := i;
    ghost var base2 := steps;
    while j < |sorted| && sorted[j] == sorted[i]
      invariant i <= j <= |sorted|
      invariant steps <= base2 + 2 * (j - i)
      decreases |sorted| - j
    {
      j := j + 1;
      steps := steps + 2;
    }
    var cnt := j - i;
    if cnt > maxCount { maxCount := cnt; }
    i := j;
    steps := steps + 3;
  }
  output := IntToString(maxCount);
  steps := steps + 1;
}
