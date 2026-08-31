// 1251_A. Broken Keyboard  (problem 960, solution 960_36)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t = int(input())
// for _ in range(t):
//     s = list(input().strip())
//     g = set()
//     n = len(s)
//     c = 1
//     if n==1:
//         print(s[0])
//     else:
//         for i in range(1,n):
//             if s[i]!=s[i-1] and c&1:
//                 g.add(s[i-1])
//             else:
//                 c += 1
//             if i==n-1 and c&1:
//                 g.add(s[i])
//         print(''.join(sorted(list(g))))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, strings: seq<string>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
