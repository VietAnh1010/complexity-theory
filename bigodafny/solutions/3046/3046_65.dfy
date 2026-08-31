// 595_A. Vitaly and Night  (problem 3046, solution 3046_65)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,m=map(int,input().split())
// l=0
// for i in range(n):
//     arr=list(map(int,input().split()))
//     j=1
//     while j<len(arr):
//         if arr[j-1]==1 or arr[j]==1:
//             l+=1
//         j+=2
// print(l)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, v_3: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
