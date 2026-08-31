// 219_A. k-String  (problem 1582, solution 1582_315)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from collections import defaultdict
// d=defaultdict(lambda:0)
// k=int(input())
// s=input()
// for i in s:
//     d[i]+=1
//     
// 
// f=1
// restring=""
// for i in range(97,123):
//     if d[chr(i)]:
//         if d[chr(i)]%k==0:
//             restring+=(chr(i)*(d[chr(i)]//k))
//             
//         else:
//             f=0
//             break
//         
// 
// print(restring*k if f else -1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(v_0: int, v_1: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
