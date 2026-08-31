// 1223_B. Strings Equalization  (problem 392, solution 392_411)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from sys import stdin, stdout
// from math import gcd
// input = stdin.readline
// 
// for _ in range(int(input())):
//     s = input()[:-1]
//     t = input()[:-1]
//     if set(s) & set(t):
//         print('YES')
//     else:
//         print('NO')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, string_pairs: seq<(string, string)>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
