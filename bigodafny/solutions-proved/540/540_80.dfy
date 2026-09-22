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

method Solve(n: int, k: int) returns (output: string, ghost steps: nat)
  requires 1 <= k <= n
  requires n % 2 == 0
  ensures steps <= 3 * n + 6
{

  var a := k;
  var parity := FloorMod(a, 2);
  var i := 1;
  steps := 1;
  if parity == 0 {
    var na := n;
    ghost var base1 := steps;
    while na != a
      invariant na >= a
      invariant (na - a) % 2 == 0
      invariant steps == base1 + 3 * ((n - na) / 2)
      decreases na - a
    {
      na := na - 2;
      i := i + 1;
      steps := steps + 3;
    }
  } else {
    var na := 1;
    ghost var base1 := steps;
    while a != na
      invariant na <= a
      invariant (a - na) % 2 == 0
      invariant steps == base1 + 3 * ((na - 1) / 2)
      decreases a - na
    {
      na := na + 2;
      i := i + 1;
      steps := steps + 3;
    }
  }
  output := IntToString(i);
  steps := steps + 1;
}
