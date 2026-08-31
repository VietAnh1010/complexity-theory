// 1463_A. Dungeon  (problem 2870, solution 2870_71)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// T = int(input())
// for i in range(0, T) :
//     a, b, c = input().split()
//     a = int(a)
//     b = int(b)
//     c = int(c)
//     Sum = a + b + c
//     if Sum % 9 == 0 and Sum / 9 <= min(a, min(b, c)) :
//         print("YES")
//     else :
//         print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, values_list: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
