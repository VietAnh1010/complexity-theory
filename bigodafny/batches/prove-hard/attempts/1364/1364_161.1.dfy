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

include "../../../../prelude.dfy"

function Pow2(e: nat): int
  ensures Pow2(e) >= 1
  decreases e
{
  if e == 0 then
    1
  else
    2 * Pow2(e - 1)
}

ghost function Pow2_steps(e: nat): nat
  decreases e
{
  2 + if e == 0 then 0 else 2 + Pow2_steps(e - 1)
}

ghost function Tri(k: nat): nat
  decreases k
{
  if k == 0 then 0 else Tri(k - 1) + k
}

ghost function FL(x: int): nat
  decreases if x < 2 then 0 else x
{
  if x < 2 then 0 else 1 + FL(x / 2)
}

lemma TriMono(j: nat, k: nat)
  requires j <= k
  ensures Tri(j) <= Tri(k)
  decreases k
{
  if j < k {
    TriMono(j, k - 1);
  }
}

lemma Pow2FL(k: nat, x: int)
  requires Pow2(k) <= x
  ensures k <= FL(x)
  decreases k
{
  if k > 0 {
    assert Pow2(k) == 2 * Pow2(k - 1);
    Pow2FL(k - 1, x / 2);
  }
}

method Solve(a: int, b: int)
    returns (output: string, ghost steps: nat)
  ensures steps <= 12 * (Tri(FL(b + 2)) + FL(b + 2)) + 6 + |output|
{
  steps := 0;
  var l := 2;
  var pos := 0;
  var powL := 4;
  var powPos := 1;
  var ans := 0;
  var done := false;
  while !done
    invariant l >= 2
    invariant 0 <= pos <= l - 2
    invariant powL == Pow2(l)
    invariant powPos == Pow2(pos)
    invariant powPos >= 1
    invariant powL >= 4
    invariant l >= 3 ==> Pow2(l - 1) <= b + 2
    invariant steps <= 12 * (Tri(l - 2) + (l - 2 - pos)) + (if done then 5 else 0)
    decreases if done then 0 else 1, if powL - 1 - powPos > b then 0 else b - (powL - 1 - powPos) + 1
  {
    steps := steps + 2;
    steps := steps + 2;
    var n := powL - 1 - powPos;
    steps := steps + 1;
    if n > b {
      done := true;
    } else {
      steps := steps + 1;
      if n >= a {
        steps := steps + 1;
        ans := ans + 1;
      }
      steps := steps + 1;
      if pos > 0 {
        assert powPos == Pow2(pos) && pos - 1 >= 0;
        assert Pow2(pos) == 2 * Pow2(pos - 1);
        steps := steps + 1;
        pos := pos - 1;
        steps := steps + 1;
        powPos := powPos / 2;
      } else {
        assert pos == 0 && Pow2(0) == 1;
        steps := steps + 1;
        l := l + 1;
        steps := steps + 1;
        pos := l - 2;
        steps := steps + 1;
        powPos := powL / 2;
        steps := steps + 1;
        powL := powL * 2;
      }
    }
  }
  steps := steps + 1;
  steps := steps + Digits(ans);
  output := IntToString(ans);
  IntToStringDigits(ans);
  if l >= 3 {
    Pow2FL(l - 1, b + 2);
  }
  TriMono(l - 2, FL(b + 2));
}

import opened Prelude
