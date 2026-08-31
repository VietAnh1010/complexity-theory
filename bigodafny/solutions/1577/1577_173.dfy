// 1155_A. Reverse a Substring  (problem 1577, solution 1577_173)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// s=input()
// f=0
// for i in range(len(s)-1):
//     if s[i+1]<s[i]:
//         print("YES")
//         print(i+1,i+2)
//         f=1
//         break
// if f==0:
//     print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, s: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
