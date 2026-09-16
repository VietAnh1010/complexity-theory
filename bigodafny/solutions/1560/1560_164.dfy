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
  requires |pairs| == n
{
  var trees := pairs;
  var felled := if n < 2 then n else 2;
  var i := 1;
  while i < n - 1
    invariant 1 <= i
    invariant |trees| == n
    decreases n - 1 - i
  {
    var left := trees[i].0 - trees[i].1;
    var right := trees[i].0 + trees[i].1;
    if left > trees[i-1].0 {
      felled := felled + 1;
    } else if right < trees[i+1].0 {
      felled := felled + 1;
      trees := trees[i := (trees[i].0 + trees[i].1, trees[i].1)];
    }
    i := i + 1;
  }
  output := IntToString(felled);
}
