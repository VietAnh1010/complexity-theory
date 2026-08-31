// 1111_A. Superhero Transformation  (problem 2436, solution 2436_612)
// time complexity: O(1)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a={*'aeiou'}
// i=input
// x,y=i(),i()
// print('YNEOS'[len(x)!=len(y) or any((u in a)^(v in a) for u,v in zip(x,y))::2])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: string, b: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
