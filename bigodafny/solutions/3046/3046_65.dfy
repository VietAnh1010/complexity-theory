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
  var l := 0;
  var i := 0;
  while i < |v_3|
    invariant 0 <= i <= |v_3|
    decreases |v_3| - i
  {
    var arr := v_3[i];
    var j := 1;
    while j < |arr|
      invariant 1 <= j
      decreases |arr| - j
    {
      if arr[j - 1] == 1 || arr[j] == 1 {
        l := l + 1;
      }
      j := j + 2;
    }
    i := i + 1;
  }
  output := IntToString(l);
}
