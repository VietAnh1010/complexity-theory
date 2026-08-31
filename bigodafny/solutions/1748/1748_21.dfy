// 1256_C. Platforms Jumping  (problem 1748, solution 1748_21)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, m, d = list(map(int, input().strip().split(' ')))
// c = list(map(int, input().strip().split(' ')))
// 
// 
// res = []
// for i, ci in enumerate(c):
//     empty = n - len(res) - sum(c[i:])
//     if empty >= d - 1:
//         res.extend(['0']*(d - 1))
//     else:
//         res.extend(['0'] * empty)
//     res.extend([str(i + 1) for _ in range(ci)])
// 
// if n - len(res) < d:
//     res.extend(['0'] * (n - len(res)))
//     print("YES")
//     print(' '.join(res))
// else:
//     print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c: int, d_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
