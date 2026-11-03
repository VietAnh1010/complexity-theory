// 611_B. New Year and Old Property  (problem 1364, solution 1364_161)
// time complexity: O(logn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// ans = 0
// a, b = map(int, input().split())
// l = 2
// pos = l-2
// ans = 0
// while True:
//     n = ((1 << l) - 1) - (1 << pos)
//     #print(l, pos, n)
//     if n > b:
//         break
//     if n >= a:
//         ans += 1
//     if pos > 0:
//         pos -= 1
//     else:
//         l += 1
//         pos = l-2
// print(ans)
//
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function Pow2(e: nat): int
  ensures Pow2(e) >= 1
  decreases e
{
  if e == 0 then 1 else 2 * Pow2(e - 1)
}

ghost function Lg(x: nat): nat  decreases x
{ if x == 0 then 0 else 1 + Lg(x / 2) }

ghost function LbOf(b: int): nat { Lg(if b > 0 then b else 0) + 2 }

lemma LgPow(x: nat)
  ensures Pow2(Lg(x)) >= x + 1
  decreases x
{
  if x > 0 { LgPow(x / 2); }
}

lemma LbBigEnough(b: int)
  ensures Pow2(LbOf(b)) >= 4 * ((if b > 0 then b else 0) + 1)
{
  var x := if b > 0 then b else 0;
  LgPow(x);
  assert Pow2(Lg(x) + 2) == 4 * Pow2(Lg(x));
}

lemma SqMono(l: nat, L: nat)
  requires 2 <= l <= L
  ensures (l - 2) * (l - 1) <= L * L
{
  assert (l - 2) * (l - 1) <= l * l;
  assert l * l <= L * L;
}

method {:isolate_assertions} Solve(a: int, b: int) returns (output: string, ghost steps: nat)
  ensures steps <= 12 * (LbOf(b) * LbOf(b)) + |output| + 20
{
  steps := 1;
  var l := 2;
  var pos := 0; // l - 2
  var powL := 4; // 2^l
  var powPos := 1; // 2^pos
  var ans := 0;
  var done := false;
  ghost var Lb := LbOf(b);
  LbBigEnough(b);
  ghost var c := 0;
  while !done
    invariant l >= 2
    invariant 0 <= pos <= l - 2
    invariant powL == Pow2(l)
    invariant powPos == Pow2(pos)
    invariant powPos >= 1
    invariant powL >= 4
    invariant 4 * powPos <= powL
    invariant powL % 4 == 0
    invariant l <= Lb
    invariant 2 * c == (l - 2) * (l - 1) + 2 * (l - 2 - pos)
    invariant steps <= 1 + 12 * c + (if done then 12 else 0)
    decreases (if done then 0 else 1), (if powL - 1 - powPos > b then 0 else b - (powL - 1 - powPos) + 1)
  {
    var n := powL - 1 - powPos;
    steps := steps + 12;
    if n > b {
      done := true;
    } else {
      assert l < Lb by {
        if l == Lb { assert powL >= 4 * ((if b > 0 then b else 0) + 1); assert n > b; }
      }
      if n >= a {
        ans := ans + 1;
      }
      if pos > 0 {
        assert powPos == Pow2(pos) && pos - 1 >= 0;
        assert Pow2(pos) == 2 * Pow2(pos - 1);
        pos := pos - 1;
        powPos := powPos / 2;
        c := c + 1;
      } else {
        assert (l - 1) * l == (l - 2) * (l - 1) + 2 * (l - 1);
        l := l + 1;
        pos := l - 2;
        powPos := powL / 2;
        powL := powL * 2;
        c := c + 1;
      }
    }
  }
  SqMono(l, Lb);
  output := IntToString(ans);
  IntToStringDigits(ans);
  steps := steps + 1 + |output|;
}
