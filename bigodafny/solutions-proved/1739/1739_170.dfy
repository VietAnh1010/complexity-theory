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
//
//
//
//
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// `a` climbs by 1 from 1 up to `half`, a value derived from the single input
// `number`; this is the value-vs-size case where the value IS the size (there
// is no separate sequence length here), so the trip count is O(|number|).
lemma HalfBound(n: int)
  ensures AbsInt(FloorDiv(n, 2)) <= AbsInt(n) + 1
{
}

method Solve(number: int) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * AbsInt(number) + 30
{
  var n := number;
  var a := 1;
  var b := 0;
  steps := 1;
  if n % 2 != 0 {
    var half := FloorDiv(n, 2);
    steps := steps + 2;
    while a < half
      invariant a <= half || a == 1
      invariant steps <= 2 * a + 3
      decreases half - a
    {
      a := a + 1;
      steps := steps + 2;
    }
    b := n - a;
    steps := steps + 1;
    HalfBound(n);
    assert a <= AbsInt(half) + 1;
    assert AbsInt(half) <= AbsInt(n) + 1;
    assert steps <= 2 * AbsInt(n) + 10;
  } else {
    var half := FloorDiv(n, 2) - 1;
    steps := steps + 3;
    while a < half
      invariant a <= half || a == 1
      invariant steps <= 2 * a + 4
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
    steps := steps + 2;
    HalfBound(n);
    assert a <= AbsInt(half) + 1;
    assert AbsInt(half) <= AbsInt(n) + 1;
    assert steps <= 2 * AbsInt(n) + 20;
  }
  output := IntToString(a) + "  " + IntToString(b);
  steps := steps + 3;
}
