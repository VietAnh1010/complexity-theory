// 1445_B. Elimination  (problem 914, solution 914_14)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t=int(input())
// for j in range(t):
// 	m=list(map(int,input().split()))
// 	a=m[0]+m[1]
// 	b=m[2]+m[3]
// 	if a>b:
// 		print(a)
// 	else:
// 		print(b)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, matrix: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
