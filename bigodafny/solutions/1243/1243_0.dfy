// 186_A. Comparing Strings  (problem 1243, solution 1243_0)
// time complexity: O(nlogn+mlogm)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// g1=list(input())
// g2=list(input())
// cntr=0
// if sorted(g1)!=sorted(g2):
//     print('NO')
// else:
//     for i in range(len(g1)):
//         if g1[i]!=g2[i]:
//                 cntr=cntr+1
//     if cntr==2:
//         print('YES')
//     else:
//         print('NO')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s1: string, s2: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
