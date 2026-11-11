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

include "../../../../prelude.dfy"

method Solve(a: int, b: int, c: int)
    returns (output: string, ghost steps: nat)
    ensures steps <= 20 * (if a > 0 then a else 0) + 20 + |output|
{
  ghost var A: int := if a > 0 then a else 0;
  ghost var it: nat := 0;
  steps := 0;
  {
    var d1 := 0;
    var d2 := 0;
    var e := 0;
    var f := a;
    while e < f
      invariant it + (if f > e then f - e else 0) <= A
      invariant steps <= 8 * it
      invariant 0 <= d1 && 0 <= d2 && d1 + d2 <= it
      decreases f - e
    {
      steps := steps + 2;
      steps := steps + 2;
      var g := (e + f) / 2;
      it := it + 1;
      steps := steps + 1;
      if g <= c {
        steps := steps + 1;
        e := g + 1;
        steps := steps + 1;
        if g < c {
          steps := steps + 1;
          d1 := d1 + 1;
        }
      } else {
        f := g;
        steps := steps + 1;
        d2 := d2 + 1;
      }
    }
    steps := steps + 1;
    var h := 1;
    steps := steps + 1;
    var i := b - 1;
    while i > b - 1 - d1
      invariant b - 1 - d1 <= i <= b - 1
      invariant steps <= 8 * it + 2 + 6 * (b - 1 - i)
      decreases i - (b - 1 - d1)
    {
      steps := steps + 4;
      steps := steps + 1;
      h := h * i;
      steps := steps + 1;
      i := i - 1;
    }
    steps := steps + 3;
    steps := steps + 1;
    var i2 := a - b;
    while i2 > a - b - d2
      invariant a - b - d2 <= i2 <= a - b
      invariant steps <= 8 * it + 6 * d1 + 6 + 6 * (a - b - i2)
      decreases i2 - (a - b - d2)
    {
      steps := steps + 4;
      steps := steps + 1;
      h := h * i2;
      steps := steps + 1;
      i2 := i2 - 1;
    }
    steps := steps + 3;
    var i3 := 1;
    while i3 < a - d1 - d2
      invariant 1 <= i3 <= A + 1
      invariant steps <= 8 * it + 6 * d1 + 6 * d2 + 9 + 6 * (i3 - 1)
      decreases a - d1 - d2 - i3
    {
      steps := steps + 4;
      steps := steps + 1;
      h := h * i3;
      steps := steps + 1;
      i3 := i3 + 1;
    }
    steps := steps + 3;
    steps := steps + (1 + Digits(h % 1000000007));
    output := IntToString(h % 1000000007);
    IntToStringDigits(h % 1000000007);
  }
}

import opened Prelude
