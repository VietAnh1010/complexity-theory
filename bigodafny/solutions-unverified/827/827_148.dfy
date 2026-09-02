// 879_A. Borya's Diagnosis  (problem 827, solution 827_148)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// arr = [[0,0] for i in range(n)]
// 
// for i in range(n):
//     arr[i][0] , arr[i][1] = map(int , input().split())
// 
// # arr.sort(key = lambda x: x[1])
// dates = [arr[0][0]]
// 
// for i,j in arr[1:]:
//     while i<=dates[-1] : i += j
//     dates.append(i)
// 
// 
// print(dates[-1])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs: seq<(int, int)>) returns (output: string)
  requires |pairs| >= 1
  requires forall k :: 0 <= k < |pairs| ==> pairs[k].1 >= 1
{
  var last := pairs[0].0;
  var idx := 1;
  while idx < |pairs|
    invariant 1 <= idx <= |pairs|
    decreases |pairs| - idx
  {
    var i := pairs[idx].0;
    var j := pairs[idx].1;
    while i <= last
      invariant j >= 1
      decreases last - i
    {
      i := i + j;
    }
    last := i;
    idx := idx + 1;
  }
  output := IntToString(last) + "\n";
}
