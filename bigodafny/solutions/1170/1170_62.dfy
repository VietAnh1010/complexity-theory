// 1425_H. Huge Boxes of Animal Toys  (problem 1170, solution 1170_62)
// time complexity: O(n)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t = int(input())
// 
// for tc in range(t):
// 
//     a, b, c, d = map(int, input().split())
// 
//     k = ["Tidak"] * 4
// 
//     if not (a+b) % 2:
//         if (b+c):
//             k[2] = "Ya"
//         if (a+d):
//             k[3] = "Ya"
//     else:
//         if (b+c):
//             k[1] = "Ya"
//         if (a+d):
//             k[0] = "Ya"
// 
//     print(*k)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, matrices: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
