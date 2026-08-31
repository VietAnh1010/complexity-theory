// 962_B. Students in Railway Carriage  (problem 566, solution 566_183)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, a, b = list(map(int, input().split()))
// row = sorted([_ for _ in input().split('*') if _], key=lambda x: len(x), reverse=True)
// 
// total = 0
// for _ in row:
// 	if a == 0 and b == 0:
// 		break
// 	l = len(_)
// 	odd, even = l // 2 + l % 2, l // 2
// 	if a > b:
// 		da = min(odd, a)
// 		db = min(even, b)
// 		total += da + db
// 		a -= da
// 		b -= db
// 	else:
// 		da = min(even, a)
// 		db = min(odd, b)
// 		total += da + db
// 		a -= da
// 		b -= db
// 
// print(total)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, m: int, s: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
