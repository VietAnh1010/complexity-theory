// 764_A. Taymyr is calling you  (problem 1738, solution 1738_24)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// m = [int(n) for n in input().split()]
// count = 0
// for i in range(1,m[2]+1):
//     if i%m[0] == 0 and i%m[1] == 0:
//         count = count + 1
// print(count)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// c is a loop-bounding VALUE, not a size -- it counts as a parameter of the
// bound (COMPLEXITY.md: value counts as parameter).
method Solve(a: int, b: int, c: int) returns (output: string, ghost steps: nat)
  requires a >= 1
  requires b >= 1
  ensures c >= 1 ==> steps <= 3 * c + 2
  ensures c < 1 ==> steps <= 2
{
  steps := 1;
  var count := 0;
  var i := 1;
  while i <= c
    invariant i >= 1
    invariant i == 1 || i <= c + 1
    invariant steps == 3 * (i - 1) + 1
    decreases c - i + 1
  {
    if i % a == 0 && i % b == 0 {
      count := count + 1;
    }
    i := i + 1;
    steps := steps + 3;
  }
  output := IntToString(count);
  steps := steps + 1;
}
