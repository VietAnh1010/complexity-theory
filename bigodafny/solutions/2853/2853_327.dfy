// 841_A. Generous Kefa  (problem 2853, solution 2853_327)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,m=list(map(int,input().split()))
// s=input()
// count={}
// for val in s:	
// 	if(val not in count):
// 		count[val]=0
// 	count[val]+=1
// flag=0
// for item in count:
// 	if(count[item]>m):
// 		flag=1
// 		break
// if(flag==0):
// 	print("YES")
// else:
// 	print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, s: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
