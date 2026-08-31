// 1283_C. Friends and Gifts  (problem 1336, solution 1336_157)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// f = [int(i) for i in input().split()]
// s = set([i for i in range(1, n + 1)])
// zero = [i for i, a in enumerate(f) if a == 0]
// x = list(s - set(f))
// for a, b in zip(zero, x):
//     f[a] = b
// for i in range(len(zero) - 1):
//     a = zero[i]
//     if f[a] == a + 1:
//         f[a] = f[zero[i + 1]]
//         f[zero[i + 1]] = a + 1
// a = zero[-1]
// if f[a] == a + 1:
//     f[a] = f[zero[0]]
//     f[zero[0]] = a + 1
// print(*f)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(N: int, tree_heights: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
