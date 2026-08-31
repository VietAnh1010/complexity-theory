// 913_C. Party Lemonade  (problem 514, solution 514_140)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, l = map(int, input().split())
// p = list(map(int, input().split()))
// d = []
// d = [[p[i] / 2**i, i + 1] for i in range(n)]
// d.sort(key = lambda x: x[0])
// res = 10**18
// q = l
// curres = 0
// for i in d:
// 	if i[1] == 1:
// 		curres += p[i[1] - 1] * q
// 		res = min(res, curres)
// 		break
// 	curb = q // 2**(i[1] - 1)
// 	curres += curb * p[i[1] - 1]
// 	res = min(res, curres + p[i[1] - 1])
// 	q %= 2**(i[1] - 1)
// print(res)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, total_score: int, scores: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
