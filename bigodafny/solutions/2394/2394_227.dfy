// 1296_E1. String Coloring (easy version)  (problem 2394, solution 2394_227)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def main():
//     n = int(input().strip())
//     s = input().strip()
//     result = []
//     a, b = "", ""
//     for c in s:
//         if c >= a:
//             a = c
//             result.append("1")
//         elif c >= b:
//             b = c
//             result.append("0")
//         else:
//             print("NO")
//             return
//     print("YES")
//     print("".join(result))
// 
// 
// main()
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, string_: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
