// 441_B. Valera and Fruits  (problem 2423, solution 2423_48)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def a():	
// 	n, v = list(map(int, input().split(" ")))
// 	d = []
// 	for i in range(n):
// 		d.append(list(map(int, input().split(" "))))
// 	d.sort()
// 
// 	cur = 0
// 	nex = 0
// 	k = 0
// 	r = 0
// 	for i in range(d[-1][0] + 2):
// 		nex = 0
// 		p = v
// 		if k != n:
// 			while(d[k][0] < i):
// 				k += 1
// 				if k == n:
// 					break
// 		if k != n:
// 			while(d[k][0] == i):
// 				nex += d[k][1]
// 				k += 1
// 				if k == n:
// 					break
// 		r += min(p, cur)
// 		p -= min(p, cur)
// 		r += min(p, nex)
// 		cur = nex - min(p, nex)
// 	return r
// 
// print(a())
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, pairs: seq<(int, int)>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
