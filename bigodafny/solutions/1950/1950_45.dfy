// 697_B. Barnicle  (problem 1950, solution 1950_45)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a, b = input().split('e')
// b = int(b)
// pos = a.find('.') + b
// a = ''.join(a.split('.'))
// a = list(a)
// while len(a) < pos:
//     a.append('0')
// a = ''.join(a[:pos]) + '.' + ''.join(a[pos:])
// if len(a) == pos + 1: a = a[:-1]
// elif len(a) > 2 and a[-2:] == '.0': a = a[:-2]
// print(a)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(coefficient: real, exponent: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
