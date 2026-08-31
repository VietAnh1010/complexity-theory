// 1385_A. Three Pairwise Maximums  (problem 276, solution 276_610)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t = int(input())
// for _ in range(t):
// 	x, y, z = map(int, input().split())
// 	if(x != y and y != z and x!= z):
// 		print("NO")
// 	elif(x == y and x != z and x == min(x, z)):
// 		print("NO")
// 	elif(y == z and y != x and y == min(y, x)):
// 		print("NO")
// 	elif(x == z and x != y and x == min(y, z)):
// 		print("NO")
// 	else:
// 		print("YES")
// 		print(min({x, y, z}), min({x, y, z}), max({x, y, z}))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, abc_list: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
