// 774_C. Maximum Number  (problem 2880, solution 2880_19)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a=int(input())
// sstring=[]
// if a%2:
//    sstring.append('7')
// else:
//    a=a
// if a%2:
//    a=a-3
// else:
//    a=a
// for i in range (a // 2):
//    sstring.append('1')
// print(''.join(sstring))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
