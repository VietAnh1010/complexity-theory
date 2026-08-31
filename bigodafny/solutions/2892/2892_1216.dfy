// 1228_A. Distinct Digits  (problem 2892, solution 2892_1216)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// x,y=map(int,input().split())
// for i in range(x,y+1,1):
//   l=[]
//   temp=i
//   while temp>0:
//       r=temp%10
//       l.append(r)
//       temp=temp//10
//   s=set(l) 
//   a=len(s)
//   b=len(l)
//   if a==b:
//       print(i)
//       break
// if a!=b:
//      print('-1')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
