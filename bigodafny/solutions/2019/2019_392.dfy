// 839_A. Arya and Bran  (problem 2019, solution 2019_392)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// _, k = map(int, input().split())
// 
// acc = 0
// result = -1
// for i, v in enumerate(map(int, input().split())):
//     acc += v
//     d = min(acc, 8) 
//     k -= d
//     acc -= d
//     if k <= 0:
//         result = i + 1
//         break
// 
// print(result)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c_list: seq<string>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
