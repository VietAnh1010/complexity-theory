// 330_B. Road Construction  (problem 698, solution 698_43)
// time complexity: O(n**2)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// impassable = []
// 
// n,m = map(int,input().split())
// 
// for i in range(m):
// 	impassable.extend(list(map(int, input().split())))
// 
// center_candidates = [x for x in range(1,n+1) if x not in impassable]
// 
// center = center_candidates[-1]
// # min number of roads
// print(n-1)
// 
// for x in range(1,n+1):
// 	if x!=center:
// 		print (center, x)
// 	
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, q: int, queries: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
