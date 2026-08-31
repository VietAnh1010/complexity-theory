// 257_B. Playing Cubes  (problem 433, solution 433_16)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def t(b, pr):
//     i, p = 1, [0, 0]
//     while b[0] or b[1]:
//         if i == 0:
//             c = pr if b[pr] else 1 - pr
//         else:
//             c = 1 - pr if b[1 - pr] else pr
//         p[c != pr] += 1
//         b[c] -= 1
//         i, pr = 1 - i, c
//     return p
// 
// n, m = map(int, input().split())
// v1, v2 = t([n - 1, m], 0), t([n, m - 1], 1)
// print(' '.join(map(str, v1 if v1[0] >= v2[0] else v2)))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method T(b0In: int, b1In: int, prIn: int) returns (p0: int, p1: int)
{
  var b0 := b0In;
  var b1 := b1In;
  var pr := prIn;
  var turn := 1;
  p0 := 0;
  p1 := 0;
  while b0 > 0 || b1 > 0
    decreases b0 + b1
  {
    var c: int;
    if turn == 0 {
      if pr == 0 {
        c := if b0 > 0 then 0 else 1;
      } else {
        c := if b1 > 0 then 1 else 0;
      }
    } else {
      if pr == 0 {
        c := if b1 > 0 then 1 else 0;
      } else {
        c := if b0 > 0 then 0 else 1;
      }
    }
    if c != pr { p1 := p1 + 1; } else { p0 := p0 + 1; }
    if c == 0 { b0 := b0 - 1; } else { b1 := b1 - 1; }
    turn := 1 - turn;
    pr := c;
  }
}

method Solve(a: int, b: int) returns (output: string)
{
  var v1p0, v1p1 := T(a - 1, b, 0);
  var v2p0, v2p1 := T(a, b - 1, 1);
  if v1p0 >= v2p0 {
    output := IntToString(v1p0) + " " + IntToString(v1p1);
  } else {
    output := IntToString(v2p0) + " " + IntToString(v2p1);
  }
}
