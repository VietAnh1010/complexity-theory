// 854_A. Fraction  (problem 1739, solution 1739_447)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// if n%4 == 0:
//     x = n//2
//     print(x-1,x+1)
// elif n % 4 == 2:
//     x = n//2
//     print(x-2,x+2)
// else:
//     x = n//2
//     print(x,x+1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(number: int) returns (output: string)
{
  if number % 4 == 0 {
    var x := number / 2;
    output := IntToString(x - 1) + " " + IntToString(x + 1);
  } else if number % 4 == 2 {
    var x := number / 2;
    output := IntToString(x - 2) + " " + IntToString(x + 2);
  } else {
    var x := number / 2;
    output := IntToString(x) + " " + IntToString(x + 1);
  }
}
