// 1003_A. Polycarp's Pockets  (problem 976, solution 976_1131)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// arr = list(map(int, input().split()))
// 
// d = dict()
// for a in arr:
//     if not a in d:
//         d[a] = 0
//     d[a] += 1
// 
// maxn = 0
// for a in d:
//     maxn = max(maxn, d[a])
// 
// print(maxn)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<string>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
