// 448_B. Suffix Structures  (problem 1675, solution 1675_150)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s=input().strip()
// t=input().strip()
// a=[s.count(chr(ord('a')+i))for i in range(26)]
// b=[t.count(chr(ord('a')+i))for i in range(26)]
// c=0
// for i in s:
//     if (c < len(t) and t[c] == i):
//         c+= 1
// if (c == len(t)):
//     print("automaton")
// elif all(a[i] == b[i] for i in range(26)):
//     print("array")
// elif all(a[i] >= b[i] for i in range(26)):
//     print("both")
// else:
//     print("need tree")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(v0: string, v1: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
