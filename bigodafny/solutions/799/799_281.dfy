// 43_B. Letter  (problem 799, solution 799_281)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a={}
// for c in input():
//     if c==" ":
//         continue
//     if c in a:
//         a[c]+=1
//     else:
//         a[c]=1
// ans="YES"
// for c in input():
//     if c==" ":
//         continue
//     if c in a:
//         if a[c]==0:
//             ans="NO"
//             break
//         else:
//             a[c]-=1
//     else:
//         ans="NO"
//         break
// print(ans)
//         
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(first_sentence: string, second_sentence: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
