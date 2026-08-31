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
  output := ""; // TODO: translate the Python above
}
