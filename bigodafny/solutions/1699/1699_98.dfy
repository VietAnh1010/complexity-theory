// 918_A. Eleven  (problem 1699, solution 1699_98)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// 
// n=int(input())
// l=[1,1]
// b=""
// for i in range(2,n+1):
// 	l.append(l[i-2]+l[i-1])
// for j in range(1,n+1):
// 	if j in l:
// 		b+="O"
// 	else:
// 		b+="o"
// print(b)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
