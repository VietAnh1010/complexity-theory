// 913_C. Party Lemonade  (problem 514, solution 514_39)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// N = 31
// n, l = map(int, input().split())
// cost = [int(x) for x in input().split()]
// for i in range(n, N):
// 	cost.append(math.inf)
// for i in range(N - 1):
// 	cost[i + 1] = min(cost[i + 1], cost[i] * 2)
// # print(cost)
// ans = math.inf
// cur_cost = 0
// for i in range(N - 1, -1, -1):
// 	# print('l = {}'.format(l))
// 	if 2**i >= l:
// 		ans = min(ans, cur_cost + cost[i])
// 	else:
// 		cur_cost += cost[i]
// 		l -= 2**i;
// 	# print('at {} and ans = {}'.format(i, ans))
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, total_score: int, scores: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
