// 877_B. Nikita and string  (problem 1952, solution 1952_87)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s=input()
// n=len(s)
// counta=[0]*(n+1)
// countb=[0]*(n+1)
// ans=0
// curra=0
// currb=0
// for i in range(n):
//   if s[i]=='a':
//     curra+=1
//   else:
//     currb+=1
//   counta[i+1]=curra
//   countb[i+1]=currb
// for i in range(n+1):
//   for j in range(i,n+1):
//     ans=max(ans,countb[j]-countb[i]+counta[i]+counta[n]-counta[j])
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
