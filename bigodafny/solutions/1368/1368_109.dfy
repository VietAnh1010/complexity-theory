// 960_A. Check the string  (problem 1368, solution 1368_109)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s=input()
// step=0
// flag=1
// suma=0;sumb=0;sumc=0
// for i in range(len(s)):
//     if s[i]!='a':
//         step=i
//         break
//     suma+=1
// for i in range(step,len(s)):
//     if s[i]!='b':
//         step=i
//         break
//     sumb+=1
// for i in range(step,len(s)):
//     if s[i]!='c':
//         flag=0
//         break
//     sumc+=1
//     step=i
// if step!=len(s)-1:
//     flag=0
// if suma>0 and sumb>0 and sumc>0 and (sumc==suma or sumc==sumb) and flag==1:
//     print('YES')
// else:
//     print('NO')
// 	 		 			 	 		 			 		 		 	 				
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
