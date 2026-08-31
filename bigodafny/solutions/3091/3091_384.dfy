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
  output := ""; // TODO: translate the Python above
}
