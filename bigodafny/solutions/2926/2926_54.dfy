// 66_D. Petya and His Friends  (problem 2926, solution 2926_54)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// isprime = [1 for i in range(2003)]
// 
// isprime[0] = 0
// isprime[1] = 0
// for i in range(2,2000,1):
//     if(isprime[i]):
//         j = i*i
//         while j < 2000:
//             isprime[j] = 0
//             j += i
// 
// prime = []
// for i in range(2,2000,1):
//     if(isprime[i]):
//         prime.append(i)
// 
// n = int(input())
// if(n==2):
//     print('-1')
//     exit(0)
// 
// for i in range(n):
//     val = 1
//     for j in range(n):
//         if i==j : continue
//         val *= prime[j]
//     print(val)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
