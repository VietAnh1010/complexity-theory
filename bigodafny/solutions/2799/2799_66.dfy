// 394_A. Counting Sticks  (problem 2799, solution 2799_66)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s=input()
// ar=[0,0,0]
// k=0
// for i in s:
//     if i=='|':
//         ar[k]+=1
//     else:
//         k+=1
// if ar[0]+ar[1]-ar[2]==0:
//     print(s)
// elif ar[0]+ar[1]-ar[2]==2:
//     if ar[0]>1:
//         print(s[1:]+s[0])
//     else:
//         s='|'*ar[0]+"+"+'|'*(ar[1]-1)+"="+'|'*(ar[2]+1)
//         print(s)
// elif ar[0]+ar[1]-ar[2]==-2:
//     if ar[2]>1:
//         print(s[-1]+s[0:len(s)-1])
//     else:
//         s='|'*ar[0]+"+"+'|'*(ar[1]+1)+"="+'|'*(ar[2]-1)
// else:
//     print("Impossible")
// 
//     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(v_0: seq<string>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
