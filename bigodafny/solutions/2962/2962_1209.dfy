// 141_A. Amusing Joke  (problem 2962, solution 2962_1209)
// time complexity: O(n**2+m**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// first = input()
// second = input()
// total = input()
// need = first + second
// if len(need) != len(total):
// 	print("NO")
// else:
// 	for letters in need:
// 		if need.count(letters) != total.count(letters): 
// 			print("NO")
// 			exit()
// 	print("YES")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(first_name: seq<string>, second_name: seq<string>, jumbled_name: seq<string>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
