// 137_B. Permutation  (problem 1413, solution 1413_104)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// ns = [int(x) for x in input().split()]
// ok = [False]*n
// for ni in ns:
//     ni-=1
//     if ni<n:
//         ok[ni]=True
// print(sum([1 for isOK in ok if not isOK]))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, values: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
