// 459_B. Pashmak and Flowers  (problem 669, solution 669_107)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// x=int(input())
// s=[int(i) for i in input().split()]
// s.sort()
// a=min(s)
// b=max(s)
// if a==b:
//     print(0,int(x*(x-1)/2))
// else:
//     A=0
//     B=0
//     for i in s:
//         if i==a:
//             A+=1
//         if i==b:
//             B+=1
//     print(b-a,int(A*B))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
