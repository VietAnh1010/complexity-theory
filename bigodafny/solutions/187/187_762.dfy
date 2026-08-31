// 984_A. Game  (problem 187, solution 187_762)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def sort(n,a):
//     list = a
//     for i in range(0,n):
//         for j in range(0,n):
//             if(list[i]>list[j]):
//                 t = list[i]
//                 list[i] = list[j]
//                 list[j] = t
//     return list
// def erase(n,a):
//     temp=1
//     list = sort(n,a)
//     t=0
//     print(a[(n)//2])
// n = int(input())
// a = [int(i) for i in input().split()]
// erase(n,a)
//             
//             
//     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  assume {:axiom} |a_list| == n;
  var arr := a_list;
  var i := 0;
  while i < n
    invariant |arr| == n
    decreases n - i
  {
    var j := 0;
    while j < n
      invariant |arr| == n
      decreases n - j
    {
      if arr[i] > arr[j] {
        var tmp := arr[i];
        arr := arr[i := arr[j]];
        arr := arr[j := tmp];
      }
      j := j + 1;
    }
    i := i + 1;
  }
  var idx := n / 2;
  assume {:axiom} 0 <= idx < |arr|;
  output := IntToString(arr[idx]);
}
