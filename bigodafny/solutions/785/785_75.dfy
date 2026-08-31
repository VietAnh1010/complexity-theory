// p03346 AtCoder Grand Contest 024 - Backfront  (problem 785, solution 785_75)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// N = int(input())
// P = [int(input()) for i in range(N)]
// 
// 
// Q = sorted([(p, i) for i, p in enumerate(P, start=1)])
// Q = [i for p, i in Q]
// 
// dp = [1] * (N + 1)
// for i in range(1, N):
//     if Q[i] > Q[i - 1]:
//         dp[i] = dp[i - 1] + 1
// 
// print(N - max(dp))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
