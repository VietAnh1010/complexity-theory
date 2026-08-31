// 1150_C. Prefix Sum Primes  (problem 3034, solution 3034_57)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// y=list(map(int,input().split()))
// if n==1:
//     print(y[0])
// else:
//     even=y.count(2)
//     odd=y.count(1)
//     if even==0 or odd==0:
//         print(*y)
//     else:
//         y=sorted(y)
//         y.reverse()
//         i=0
//         while i<n:
//             if y[i]==1:
//                 break
//             i+=1
//         t=y[i]
//         y[i]=y[1]
//         y[1]=t
//         print(*y)
//         
//                 
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
