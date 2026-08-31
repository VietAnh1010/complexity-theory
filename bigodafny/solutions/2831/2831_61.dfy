// 769_B. News About Credit  (problem 2831, solution 2831_61)
// time complexity: O(n**2)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// 
// a = list(map(int, input().split()))
// 
// p = a[0]
// a = [(p, 0)] + sorted([(a[i], i) for i in range(1, n)], reverse=True)
// 
// result = ""
// 
// got = {0}
// 
// for i in range(n):
// 	temp_a = a[i][0]
// 	temp_i = i + 1
// 
// 	while temp_a > 0 and temp_i < n:
// 		if temp_i not in got:
// 			got.add(temp_i)
// 			temp_a -= 1
// 			result += str(a[i][1] + 1) + " " + str(a[temp_i][1] + 1) + "\n"
// 
// 		temp_i += 1
// 
// if len(got) < n:
// 	print(-1)
// else:
// 	print(n - 1)
// 	print(result)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
