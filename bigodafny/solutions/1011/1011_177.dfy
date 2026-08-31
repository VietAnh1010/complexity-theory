// 1099_B. Squares and Segments  (problem 1011, solution 1011_177)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// 
// rt = n**0.5
// 
// if rt % 1> 0.5:
// 	b = int(rt) + 1
// else:
// 	b = int(rt)
// 
// # if rt * rt == n:
// # 	print(int(rt) * 2)
// # else:
// # 	if n > a * b:
// # 		print(max(a,b) * 2)
// # 	else:
// # 		print(a + b)
// 
// q = n // b
// if n % b != 0:
// 	q += 1
// 
// print(q + b)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
