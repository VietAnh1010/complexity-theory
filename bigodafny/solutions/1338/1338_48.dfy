// 1261_B1. Optimal Subsequences (Easy Version)  (problem 1338, solution 1338_48)
// time complexity: O(n+mlogm)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = [int(i) for i in input().split()]
// b = [(a[i], n - i) for i in range(n)]
// b.sort(reverse=True)
// b = [(b[i][0], n - b[i][1]) for i in range(n)]
// 
// m = int(input())
// for qu in range(m):
//     k, p = map(int, input().split())
//     c = b[:k]
//     c.sort(key = lambda x: x[1])
//     print(c[p-1][0])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>, q: int, queries: seq<(int, int)>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
