// 1023_C. Bracket Subsequence  (problem 1935, solution 1935_61)
// time complexity: O(n+m)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// R = lambda:list(map(int,input().split()))
// n,t = R()
// s = input()
// 
// st = []
// req = n-t
// flag = 0
// for x in s:
//     if(x==")" and flag==0 and req>0):
//         req-=2
//         st.pop()
//         if(req==0):
//             flag = 1
//     else:
//         st.append(x)
// print("".join(st))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, s: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
