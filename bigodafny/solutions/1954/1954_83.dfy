// p02927 Japanese Student Championship 2019 Qualification - Takahashi Calendar  (problem 1954, solution 1954_83)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// M,D=map(int,input().split())
// cnt=0
// for i in range(1,M+1):
//     for j in range(1,D+1):
//         iti=j%10
//         ju=j//10
//         if iti>=2 and ju>=2 and i==iti*ju:
//             cnt+=1
// 
// print(cnt)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
