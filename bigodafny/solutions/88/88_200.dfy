// 1202_A. You Are Given Two Binary Strings...  (problem 88, solution 88_200)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// for u in range(int(input())):
//     x=input()[::-1]
//     y=input()[::-1]
//     a,b=0,0
//     for i in range(len(y)):
//         if(y[i]=='1'):
//             a=i+1
//             break
//     for i in range(len(x)):
//         if(x[i]=='1' and i+1>=a):
//             b=i+1
//             break
//     print(b-a)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, string_list: seq<string>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
