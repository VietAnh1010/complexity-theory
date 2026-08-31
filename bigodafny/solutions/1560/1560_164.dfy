// 545_C. Woodcutters  (problem 1560, solution 1560_164)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// trees = []
// for i in range(n):
// 	x, h = map(int, input().split())
// 	trees.append((x, h))
// felled = min(2, n)
// for i in range(1,n-1):
// 	left = trees[i][0] - trees[i][1]
// 	right = trees[i][0] + trees[i][1]
// 	if left > trees[i-1][0]:
// 		felled += 1
// 	elif right < trees[i+1][0]:
// 		felled += 1
// 		trees[i] = (trees[i][0] + trees[i][1], trees[i][1])
// print(felled)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs: seq<(int, int)>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
