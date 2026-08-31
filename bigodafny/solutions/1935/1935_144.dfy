// 1023_C. Bracket Subsequence  (problem 1935, solution 1935_144)
// time complexity: O(n+m)log(n+m)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// aa,bb=map(int, input().split())
// s=input()
// kiri=[]
// tupl=[]
// ini=[]
// cetak=""
// for i in range(len(s)):
// 	if s[i]=="(":
// 		kiri.append(i)
// 	else:
// 		tupl.append((kiri.pop(),i))
// tupl=tupl[:bb//2]
// for k in tupl:
// 	ini.extend(k)
// ini.sort()
// for j in ini:
// 	cetak+=s[j]
// print(cetak)
// 			   	 	   	  		 	 	 		 				 	
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, s: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
