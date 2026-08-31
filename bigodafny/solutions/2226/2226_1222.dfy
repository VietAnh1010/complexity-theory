// 978_B. File Name  (problem 2226, solution 2226_1222)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// string = input()
// 
// counter = int()
// 
// result = int()
// 
// for letter in string:
// 	if letter == 'x':
// 		counter += 1
// 
// 		if counter >= 3:
// 			result += 1
// 	else:
// 		counter = 0
// 
// print(result)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, binary_string: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
