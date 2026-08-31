// 1421_C. Palindromifier  (problem 450, solution 450_276)
// time complexity: O(n)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def isPalin(st):
//     
//     i,j=0,len(st)-1
//     while(i<=j):
//         if(st[i]==st[j]):
//             i+=1
//             j-=1
//         else:
//             return False
//     return True
// 
//         
// def proC(st):
//     if(isPalin(st)):
//         print(0)
//         return 
//     print(3)
//     print('R',len(st)-1)
//     print('L',len(st))
//     print('L',2)
// n=input()
// proC(n)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
