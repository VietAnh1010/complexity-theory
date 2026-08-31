// 1373_E. Sum of Digits  (problem 554, solution 554_70)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// sys.setrecursionlimit(10**7)
// 
// for _ in range(int(input())):
// 	N, K = map(int, input().split());ans = float("inf")
// 	for i in range(100 - K):
// 		val = 0
// 		for j in range(i, i + K + 1):val += sum(list(map(int, list(str(j)))))
// 		if (N - val) % (K + 1) == 0 and N >= val:x = int((N - val) // (K + 1));tail = str(x % 9) + str("9") * int(x // 9);ans = min(ans, (int(tail + "0" + str(i)) if i < 10 else int(tail + str(i))))
// 
// 	print(-1) if ans == float("inf") else print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs: seq<(int, int)>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
