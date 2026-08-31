// 1271_B. Blocks  (problem 2516, solution 2516_238)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = input()
// 
// 
// def go(s, x):
//   b = [1 if c == 'B' else 0 for c in s]
//   o = []
//   n = len(b)
//   for i in range(n):
//     if b[i] != x:
//       if i + 1 >= n:
//         return 0
//       o += i + 1,
//       b[i + 1] = b[i + 1] ^ 1
//   print(len(o))
//   print(' '.join(map(str, o)))
//   return 1
// 
// 
// if not go(a, 0) and not go(a, 1):
//   print(-1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, is_white_list: seq<bool>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
