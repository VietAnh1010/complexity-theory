// 53_A. Autocomplete  (problem 1196, solution 1196_51)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s = input()
// n = int(input())
// l = []
// for i in range(n):
// 	l.append(input())
// k = len(s)
// answer = ""
// for a in l:
// 	if a[:k]==s:
// 		if a<answer or answer =="":
// 			answer=a
// if answer:
// 	print(answer)
// else:
// 	print(s)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(text: string, n: int, text_list: seq<string>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
