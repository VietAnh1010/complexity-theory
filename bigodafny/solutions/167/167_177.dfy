// 1184_A1. Heidi Learns Hashing (Easy)  (problem 167, solution 167_177)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// n = int(input())
// x = math.floor(math.sqrt(n))
// p = 0
// for i in range(1, x):
// 	if (n-1-i**2-i)%(2*i) == 0 :
// 		print(i,  (n-1-i**2-i)//(2*i))
// 		p = 1
// 		break
// if not p:
// 	print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
