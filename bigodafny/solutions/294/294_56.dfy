// p03687 AtCoder Grand Contest 016 - Shrinking  (problem 294, solution 294_56)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s = input()
// exitLower = list(set(list(s)))
// m = len(s)
// 
// for alp in exitLower:
//     SL = list(s)
//     cnt = 0
//     while len(set(SL)) > 1:
//         for i in range(len(SL)-1):
//             if SL[i+1] == alp:
//                 SL[i] = alp
//         SL.pop()
//         cnt += 1
//     m = min(m,cnt)
// 
// print(m)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
