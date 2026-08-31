// 9_C. Hexadecimal's Numbers  (problem 2381, solution 2381_156)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def main():
// 	n = int(input())
// 	print(calculate(n))
// 
// def helper(s):
// 	if len(s) == 0:
// 		return 1
// 	num = int(s[0])
// 	if num == 0:
// 		return helper(s[1:])
// 	elif num == 1:
// 		return 2**(len(s) - 1) + helper(s[1:])
// 	elif num >= 2:
// 		return 2**len(s) 
// 	else:
// 		assert(False)
// 
// def calculate(n):
// 	return helper(str(n)) - 1
// 
// main()
// #print(calculate(13402))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
