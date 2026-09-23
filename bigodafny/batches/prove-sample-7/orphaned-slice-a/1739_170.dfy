// 854_A. Fraction  (problem 1739, solution 1739_170)
// time complexity: O(n)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// n=int(input())
// if (n%2)!=0:
//     a=1
//     while a < math.floor(n/2):
//         a+=1
//     b=n-a
//     print(f"{a}  {b}")
// else:
//     a=1
//     while a < math.floor(n/2)-1:
//         a+=1
//     b=n-a
//     if a%2==0 and b%2==0:
//         a=a-1
//         b=b+1
//     print(f"{a}  {b}")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// The loop counts up to floor(n/2) (or one less), a quantity bounded by the
// input VALUE n, not by any sequence length. Per the value-counts-as-a-
// parameter convention, that bound is charged as n itself, giving O(n).
method Solve(number: int) returns (output: string, ghost steps: nat)
  requires number >= 0
  ensures steps <= 2 * number + 6
{
  var n := number;
  var a := 1;
  var b := 0;
  steps := 1;
  if n % 2 != 0 {
    var half := FloorDiv(n, 2);
    while a < half
      invariant 1 <= a
      invariant half > 0 ==> a <= half + 1
      invariant half <= 0 ==> a == 1
      invariant half <= n
      invariant steps <= 1 + 2 * (a - 1)
      decreases half - a
    {
      a := a + 1;
      steps := steps + 2;
    }
    b := n - a;
    steps := steps + 1;
  } else {
    var half := FloorDiv(n, 2) - 1;
    while a < half
      invariant 1 <= a
      invariant half > 0 ==> a <= half + 1
      invariant half <= 0 ==> a == 1
      invariant half <= n
      invariant steps <= 1 + 2 * (a - 1)
      decreases half - a
    {
      a := a + 1;
      steps := steps + 2;
    }
    b := n - a;
    steps := steps + 1;
    if a % 2 == 0 && b % 2 == 0 {
      a := a - 1;
      b := b + 1;
      steps := steps + 2;
    }
  }
  output := IntToString(a) + "  " + IntToString(b);
  steps := steps + 3;
}
