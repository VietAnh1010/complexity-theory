// 1323_C. Unusual Competitions  (problem 661, solution 661_47)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n= int(input())
// seq= list(input())
// 
// if seq.count(')')!=seq.count('('):
// 	print(-1)
// else:
// 	a,b=[],[]
// 	for i in range(len(seq)):
// 		if seq[i]==')':
// 			a.append(i)
// 		else:
// 			b.append(i)
// 	c=[]
// 	for i in range(len(a)):
// 		if b[i]>a[i]:
// 			c.append(a[i])
// 			c.append(b[i])
// 	c.sort()
// 	start=0
// 	sum=0
// 	for i in range(len(c)-1):
// 		if c[i]!=c[i+1]-1:
// 			sum+=c[i]-c[start]+1
// 			start=i+1
// 		else:
// 			if i==len(c)-2:
// 				sum+=c[i+1]-c[start]+1
// 			
// 	print(sum)
// 	
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, s: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
