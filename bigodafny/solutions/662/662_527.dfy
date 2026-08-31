// 1342_B. Binary Period  (problem 662, solution 662_527)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// # list( map(int, input().split()) )
// rw = int(input())
// for ewqr in range(rw):
//     t = input()
//     if t.count('1') == 0 or t.count('0') == 0:
//         print(t)
//         continue
//     s = '01' * len(t)
//     print(s)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, binary_strings: seq<string>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
