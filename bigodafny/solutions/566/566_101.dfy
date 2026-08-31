// 962_B. Students in Railway Carriage  (problem 566, solution 566_101)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, a, b = map(int, input().split(' '))
// tot = a + b
// lens = [len(s) for s in input().split('*')]
// 
// for l in lens:
//     if a > b:
//         if l % 2 == 1:
//             a -= min(a, (l+1)//2)
//         else:
//             a -= min(a, l//2)
//         b -= min(b, l//2)
//     else:
//         a -= min(a, l//2)
//         if l % 2 == 1:
//             b -= min(b, (l+1)//2)
//         else:
//             b -= min(b, l//2)
// 
// print(tot - a - b)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, m: int, s: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
