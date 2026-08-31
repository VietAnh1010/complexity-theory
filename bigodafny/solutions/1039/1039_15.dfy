// 1004_C. Sonya and Robots  (problem 1039, solution 1039_15)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from collections import defaultdict
// from bisect import bisect
// 
// INF = 10**9
// 
// n = int(input())
// a = list(map(int, input().split()))
// 
// first_pos = [INF] * (n+1)
// for i, x in enumerate(a):
//     if first_pos[x] == INF:
//         first_pos[x] = i
//         
// last_pos = [-1] * (n+1)
// for i, x in enumerate(a):
//     last_pos[x] = i
// last_pos.sort()
// 
// total = 0
// for i, first in enumerate(first_pos):
//     total += len(last_pos) - bisect(last_pos, first)
// print(total)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n_str: string, a_list_str: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
