// 1099_B. Squares and Segments  (problem 1011, solution 1011_177)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// 
// rt = n**0.5
// 
// if rt % 1> 0.5:
// 	b = int(rt) + 1
// else:
// 	b = int(rt)
// 
// # if rt * rt == n:
// # 	print(int(rt) * 2)
// # else:
// # 	if n > a * b:
// # 		print(max(a,b) * 2)
// # 	else:
// # 		print(a + b)
// 
// q = n // b
// if n % b != 0:
// 	q += 1
// 
// print(q + b)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
  requires n >= 1
{
  var f := 0;
  while (f + 1) * (f + 1) <= n
    invariant 0 <= f
    invariant f * f <= n
    invariant f <= n
    decreases n - f
  {
    f := f + 1;
  }
  var b := f;
  if 4 * n > (2 * f + 1) * (2 * f + 1) {
    b := f + 1;
  }
  var q := n / b;
  if n % b != 0 { q := q + 1; }
  output := IntToString(q + b);
}
