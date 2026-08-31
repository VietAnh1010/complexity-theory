// 633_A. Ebony and Ivory  (problem 1678, solution 1678_212)
// time complexity: O(n)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a, b, c = map(int, input().split())
// ok = False
// for i in range(c//a+1):
//     #print(c-a*i)
//     #print((c-a*i)%b==0)
//     if c-a*i >= 0 and (c-a*i)%b==0:
//         ok = True
// if ok:
//     print("Yes")
// else:
//     print("No")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(rows: int, columns: int, value: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
