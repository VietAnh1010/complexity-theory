// p02417 Counting Characters  (problem 3005, solution 3005_182)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import string
// a = ""
// 
// 
// while True:
//     try:
//         a += input().lower()
//     except Exception:
//         break
// 
// 
// for i in string.ascii_lowercase:
//     print(f"{i} : {a.count(i)}")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(text: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
