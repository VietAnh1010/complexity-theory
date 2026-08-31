// 348_A. Mafia  (problem 1626, solution 1626_179)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// 
// n = int(input())
// a = [int(x) for x in input().split()]
// a.sort(reverse=True)
// low = a[0]
// high = sum(a)
// while low < high:
// 	mid = (low + high) // 2
// 	t = 0
// 	i = 0
// 	while i < n and t < mid:
// 		if t >= a[i]:
// 			t = mid
// 			break
// 		t += (mid - a[i])
// 		i += 1
// 	if t >= mid:
// 		high = mid
// 	else:
// 		low = mid + 1
// print(high)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
