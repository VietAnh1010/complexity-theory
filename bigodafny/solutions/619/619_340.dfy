// 975_A. Aramic script  (problem 619, solution 619_340)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// s = list(input().split())
// dic = dict()
// for i in s:
//     l2 = list(set(list(i)))
//     l2.sort()
//     l2 = ''.join(l2)
//     if l2 in dic:
//         pass
//     else:
//         dic[l2] = 1
// c = 0
// #print(dic)
// for i in dic:
//     c+=1
// print(c)
//     
//         
//     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, strings: seq<string>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
