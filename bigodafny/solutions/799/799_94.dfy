// 43_B. Letter  (problem 799, solution 799_94)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// 
// a = list(input())
// 
// 
// b =(input())
// h=0
// 
// for k in b:
//     if k!=' ':
//         if k in a:
//             a.remove(k)
//         else:
//             print('NO')
//             h+=1
//             break
// 
// 
// if h==0:
//     print('YES')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(first_sentence: string, second_sentence: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
