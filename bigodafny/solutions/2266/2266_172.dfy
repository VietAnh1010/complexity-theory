// 296_A. Yaroslav and Permutations  (problem 2266, solution 2266_172)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = list(map(int, input().split()))
// mx = 0
// for i in a: mx = max(mx, a.count(i))
// if n%2==1:
//     if mx>(n//2)+1: print('NO')
//     else: print('YES')
// else:
//     if mx>n//2: print('NO')
//     else: print('YES')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<string>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
