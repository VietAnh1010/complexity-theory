// 501_B. Misha and Changing Handles  (problem 2217, solution 2217_247)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// q = int(input())
// n = [input() for x in range(q)]
// a = [n[0].split(), ]
// for x in range(1, q):
//     f = False
//     s = n[x].split()
//     for y in a:
//         if s[0] == y[-1]:
//             y.append(s[1])
//             f = True
//             break
//     if not f:
//         a.append(s)
// print(len(a))
// for x in a:
//     print(x[0], x[-1])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, handles: seq<string>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
