// 432_A. Choosing Teams  (problem 2166, solution 2166_288)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, k = map(int,input().split())
// y = map(int,input().split())
// z = sorted(y)
// k = 5-k
// if(k<0):
// 	print("0")
// else:
// 	count = 0
// 	for i in z:
// 		if(i<=k):
// 			count = count+1
// print(int(count/3))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, numbers: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
