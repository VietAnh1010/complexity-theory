// 1436_C. Binary Search  (problem 1359, solution 1359_4)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// a, b, c = map(int, input().split())
// d1 = 0
// d2 = 0
// e = 0
// f = a
// while e < f:
//     g = (e + f) // 2
//     if g <= c:
//         e = g + 1
//         if g < c:
//             d1 += 1
//     else:
//         f = g
//         d2 += 1
// h = 1
// for i in range (b - 1, b - 1 - d1, -1):
//     h *= i
// for i in range (a - b, a - b - d2, -1):
//     h *= i
// for i in range (1, a - d1 - d2):
//     h *= i
// print(h % 1000000007)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// a is a value (array size), not a size parameter -- but every loop here is
// bounded directly by a (the binary-search loop shrinks a range starting at
// a, and the three product loops together walk at most d1 + d2 + (a-d1-d2)
// <= a steps total), so the whole method is O(a). h accumulates a product
// of up to a factors each as large as a itself, so the true CPython cost of
// `h *= i` grows with the bit-length of h -- the charge table's flat cost
// for `int` arithmetic does not see that growth, so this bound is tighter
// than the label's O(n**2), not a disagreement with it.
method Solve(a: int, b: int, c: int) returns (output: string, ghost steps: nat)
  requires a >= 0
  ensures steps <= 2 * a + |output| + 20
{
  steps := 1;
  var d1 := 0;
  var d2 := 0;
  var e := 0;
  var f := a;
  ghost var cnt1 := 0;
  while e < f
    invariant 0 <= e <= f <= a
    invariant cnt1 == steps - 1
    invariant cnt1 + (f - e) <= a
    invariant d1 + d2 <= cnt1
    decreases f - e
  {
    var g := (e + f) / 2;
    if g <= c {
      e := g + 1;
      if g < c { d1 := d1 + 1; }
    } else {
      f := g;
      d2 := d2 + 1;
    }
    cnt1 := cnt1 + 1;
    steps := steps + 1;
  }
  assert steps <= 1 + a;
  assert d1 + d2 <= a;
  var h := 1;
  var i := b - 1;
  ghost var base2 := steps;
  while i > b - 1 - d1
    invariant b - 1 - d1 <= i <= b - 1
    invariant steps <= base2 + ((b - 1) - i)
    decreases i - (b - 1 - d1)
  {
    h := h * i;
    i := i - 1;
    steps := steps + 1;
  }
  assert steps <= base2 + d1;
  var i2 := a - b;
  ghost var base3 := steps;
  while i2 > a - b - d2
    invariant a - b - d2 <= i2 <= a - b
    invariant steps <= base3 + ((a - b) - i2)
    decreases i2 - (a - b - d2)
  {
    h := h * i2;
    i2 := i2 - 1;
    steps := steps + 1;
  }
  assert steps <= base3 + d2;
  var i3 := 1;
  ghost var base4 := steps;
  while i3 < a - d1 - d2
    invariant 1 <= i3 <= a - d1 - d2 + 1
    invariant steps <= base4 + (i3 - 1)
    decreases (a - d1 - d2) - i3
  {
    h := h * i3;
    i3 := i3 + 1;
    steps := steps + 1;
  }
  assert steps <= base4 + (a - d1 - d2);
  assert steps <= (1 + a) + d1 + d2 + (a - d1 - d2);
  assert steps <= 1 + 2 * a;
  output := IntToString(h % 1000000007);
  steps := steps + |output| + 2;
}
