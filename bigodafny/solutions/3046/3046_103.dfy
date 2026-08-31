// 595_A. Vitaly and Night  (problem 3046, solution 3046_103)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, m = map(int, input().split())
// 
// ans = 0
// for _ in range(n):
// 	windows = list(map(int, input().split()))
// 	ans += sum(min(1, windows[i] + windows[i + 1]) for i in range(0, m * 2, 2))
// 
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, v_3: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
