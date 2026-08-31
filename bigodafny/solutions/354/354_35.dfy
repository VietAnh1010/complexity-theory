// 628_A. Tennis Tournament  (problem 354, solution 354_35)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a,b,c=map(int,input().split())
// m=(a-1)*(2*b+1)
// n=a*c
// print(m,n)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c: int) returns (output: string)
{
  var m := (a - 1) * (2 * b + 1);
  var n := a * c;
  output := IntToString(m) + " " + IntToString(n);
}
