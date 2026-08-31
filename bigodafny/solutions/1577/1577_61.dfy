// 1155_A. Reverse a Substring  (problem 1577, solution 1577_61)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// s = input()
// s = [i for i in s]
// z = sorted(s)
// if z == s:
//     print("NO")
// else:
//     for i in range(n-1):
//         if ord(s[i]) > ord(s[i+1]):
//             print("YES")
//             print(i+1, i+2) 
//             break
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, s: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
