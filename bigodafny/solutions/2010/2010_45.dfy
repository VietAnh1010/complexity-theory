// 1201_B. Zero Array  (problem 2010, solution 2010_45)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def check(l):
// 	s = sum(l)
// 	for i in l:
// 		if s-i < i:
// 			return "NO"
// 	if s%2:
// 		return ("NO")
// 	else:
// 		return ("YES")
// 
// n = int(input())
// l = list(map(int,input().split()))
// 
// print(check(l))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
