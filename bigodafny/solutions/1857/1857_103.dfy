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

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var sorted := SortInts(a_list);
  var maxCount := 0;
  var i := 0;
  while i < |sorted|
    decreases |sorted| - i
  {
    var j := i;
    while j < |sorted| && sorted[j] == sorted[i]
      decreases |sorted| - j
    {
      j := j + 1;
    }
    var cnt := j - i;
    if cnt > maxCount { maxCount := cnt; }
    i := j;
  }
  output := IntToString(maxCount);
}
