// 467_A. George and Accommodation  (problem 3091, solution 3091_384)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// a=[]
// count=0
// for x in range(n):
//     a+=list(map(int,input().split()))
// i=0
// while i<n*2:
//     if abs(a[i]-a[i+1])>=2:
//         count+=1
//     i+=2
// print(count)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs_list: seq<seq<int>>) returns (output: string)
{
  var a: seq<int> := [];
  var i := 0;
  while i < |pairs_list|
    invariant 0 <= i <= |pairs_list|
    decreases |pairs_list| - i
  {
    a := a + pairs_list[i];
    i := i + 1;
  }
  var count := 0;
  var idx := 0;
  while idx + 1 < |a|
    invariant 0 <= idx
    decreases |a| - idx
  {
    if AbsInt(a[idx] - a[idx + 1]) >= 2 {
      count := count + 1;
    }
    idx := idx + 2;
  }
  output := IntToString(count);
}
