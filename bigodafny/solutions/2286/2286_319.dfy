// 630_F. Selection of Personnel  (problem 2286, solution 2286_319)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def fac(x):
// 	p = 1
// 	for i in range(2, x + 1):
// 		p *= i
// 	return p
// 
// 
// def c(n, k):
// 	return fac(n) // (fac(k) * fac(n - k))
// 
// n = int(input())
// print(c(n, 5) + c(n, 6) + c(n, 7))
// 
//  	 								 	     			   	 		 		
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
