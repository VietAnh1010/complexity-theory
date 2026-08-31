// 999_A. Mishka and Contest  (problem 1470, solution 1470_325)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a,b = map(int,input().split())
// l= [int(i) for i in input().split()]
// 
// c=0
// while len(l)>0:
//     premier = l[0]
//     last= l[-1]
//     if premier<=b:
//         c+=1
//         del l[0]
//     elif last<=b:
//         c+=1
//         del l[-1]
//     else:
//         break
// 
// print(c)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
