// 281_B. Nearest Fraction  (problem 696, solution 696_49)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from fractions import Fraction
// 
// x,y,n = map(int, input().split(" "))
// f=Fraction(x,y).limit_denominator(n)
// a=f.numerator
// b=f.denominator
// print(str(a)+"/"+str(b))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(v_0: int, v_1: int, v_2: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
