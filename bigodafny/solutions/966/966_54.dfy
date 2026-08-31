// 596_A. Wilbur and Swimming Pool  (problem 966, solution 966_54)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from sys import stdin
// n=int(stdin.readline().strip())
// s=[]
// for i in range(n):
//     
//     a,b=map(int,stdin.readline().strip().split())
//     s.append([a,b])
// ans=-1
// for i in range(n):
//     for j in range(i+1,n):
//         if( s[i][0]!=s[j][0] and  s[i][1]!=s[j][1] ):
//             
//             ans=abs(s[i][0]-s[j][0] )*  abs(s[i][1]-s[j][1] )  
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, values: seq<seq<string>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
