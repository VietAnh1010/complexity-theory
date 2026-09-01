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

method Solve(a: int, b: int, c: int) returns (output: string)
{
{

  var d1 := 0;
  var d2 := 0;
  var e := 0;
  var f := a;
  while e < f
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
  }
  var h := 1;
  var i := b - 1;
  while i > b - 1 - d1
    decreases i - (b - 1 - d1)
  {
    h := h * i;
    i := i - 1;
  }
  var i2 := a - b;
  while i2 > a - b - d2
    decreases i2 - (a - b - d2)
  {
    h := h * i2;
    i2 := i2 - 1;
  }
  var i3 := 1;
  while i3 < a - d1 - d2
    decreases (a - d1 - d2) - i3
  {
    h := h * i3;
    i3 := i3 + 1;
  }
  output := IntToString(h % 1000000007);
}
}
