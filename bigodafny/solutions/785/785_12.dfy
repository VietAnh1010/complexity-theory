// p03346 AtCoder Grand Contest 024 - Backfront  (problem 785, solution 785_12)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// P = list(int(input()) for _ in range(n))
// tmp = [0]*(n+1)
// for p in P:
//     tmp[p] = tmp[p-1] + 1
// print(n-max(tmp))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
