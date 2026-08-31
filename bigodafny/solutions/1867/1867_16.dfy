// 1202_D. Print a 1337-string...  (problem 1867, solution 1867_16)
// time complexity: O(n)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import bisect
// 
// Q=int(input())
// 
// A=[n*(n-1)//2 for n in range(10**5)]
// 
// 
// x=bisect.bisect(A,10**9)
// 
// 
// for testcases in range(Q):
//     t=int(input())
// 
//     if t==1:
//         print(1337)
//         continue
// 
//     x=bisect.bisect_left(A,t)
// 
//     ANS="1"+"3"*(x-1-2)+"1"*(t-(A[x-1]))+"337"
// 
//     print(ANS)
//     
//     
//     
//     
//     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
