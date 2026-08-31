// 1385_A. Three Pairwise Maximums  (problem 276, solution 276_1206)
// time complexity: O(n*m)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// for i in range(int(input())):
//     ls=[int(a) for a in input().split()]
//     ls1=[1]*3
//         
//     if ls.count(max(ls))>1:
//         if ls.count(max(ls))==3:
//             ls1=ls
//         else:
//             ls1[ls.index(min(ls))]=min(ls)
//             ls1[ls.index(min(ls))-1]=max(ls)
//         
//         print("YES")
//         for _ in range(3):
//             print(ls1[_], end=' ' )
//         print('\n')
//     else:
//         print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, abc_list: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
