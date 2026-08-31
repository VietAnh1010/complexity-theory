// 1184_A1. Heidi Learns Hashing (Easy)  (problem 167, solution 167_191)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def calculate(n):
//   if (n < 5) or (n%2 == 0):
//     return 'NO'
//   else:
//     y = int((n-3)/2)
//     return "1 "+str(y)
// 
// print (calculate(int(input())))
// 				 	 		   				 	 	  	  		 		
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
