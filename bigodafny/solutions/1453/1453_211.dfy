// 1197_B. Pillars  (problem 1453, solution 1453_211)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def f(l):
//     for i in range(len(l)-1):
//         if l[i] > l[i+1]:
//             break
//     #print(i+1)
//     if sorted(l[i+1:],reverse=True) == l[i+1:]:return 0
//     return 1
// 
// M = 10**9 + 7
// R = lambda: map(int, input().split())
// n = int(input())
// L = list(R())
// if len(set(L)) != n:print("NO")
// else:print("YNEOS"[f(L)::2])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
