// 1251_A. Broken Keyboard  (problem 960, solution 960_63)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// r = []
// for i in ' '*n:
//   s = input()
//   m = []
//   t = set()
//   j = 0
//   while j < len(s):
//     if s[j] not in t:
//       c = 1
//       while j < len(s)-1 and s[j] == s[j+1]:
//         j += 1
//         c += 1
//       if c % 2 == 1:
//         t.add(s[j])
//     j += 1
//   r += [t]
// for i in r:
//   print(*sorted(i), sep='')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, strings: seq<string>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
