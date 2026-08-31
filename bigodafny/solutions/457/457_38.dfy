// 355_A. Vasya and Digital Root  (problem 457, solution 457_38)
// time complexity: O(n**2)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// l=input().split()
// k=int(l[0])
// d=int(l[1])
// if(k==1 and d==0):
// 	print(0)
// elif(k!=1 and d==0):
// 	print('No solution')
// else:
// 	i=1
// 	n=d
// 	while len(str(n))!=k:
// 		n+=9**(i)
// 		i+=1
// 	print(n)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
