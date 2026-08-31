// 638_A. Home Numbers  (problem 540, solution 540_80)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, a = map(int,input().split())
// k = a % 2
// i = 1
// if k == 0:
//     na=n
//     while na!=a:
//         na = na-2
//         i +=1
// else:
//     na = 1
//     while a!=na:
//         na += 2
//         i+=1
// print(i)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
