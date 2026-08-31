// 1105_B. Zuhair and Strings  (problem 2231, solution 2231_194)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,k=input().split()
// n=int(n)
// k=int(k)
// s=input()
// 
// 
// arr=[]
// f=s[0]
// z=''
// for i in range (len(s)):
//     if s[i]==f:
//         z=z+s[i]
//     else:
//         f=s[i]
//         arr.append(z)
//         z=f
// arr.append(z)
// arr
// 
// arr.sort()
// 
// f=arr[0][0]
// c=0
// i=0
// q=[]
// while i<len(arr):
//     if f in arr[i]:
//         c=c+int(len(arr[i])/k)
//     else:
//         q.append(c)
//         c=0
//         
//         f=arr[i][0]
//         i=i-1
//         pass
//     i=i+1
// q.append(c)
// 
// print(max(q))
//         
//         
//         
//         
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, string_: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
