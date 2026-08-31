// 1299_A. Anu Has a Function  (problem 2465, solution 2465_139)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// vals = list(map(int, input().split()))
// pref, suff = [0] * (n + 1), [0] * (n + 1)
// for i in range(n):
//     pref[i + 1] = pref[i] | vals[i]
//     suff[n - i - 1] = suff[n - i] | vals[n - i - 1]
// ret = (-float('inf'), -float('inf'))
// for i, a in enumerate(vals):
//     b = pref[i] | suff[i + 1]
//     ret = max(ret, ((a | b) - b, i))
// print(*[vals[ret[1]]] + [v for i, v in enumerate(vals) if i != ret[1]])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(t: int, n_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
