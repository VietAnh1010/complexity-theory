// --- Python ---------------------------------------------------------
// from math import inf,floor,ceil
// x,y,n=map(float,input().split())
// m=inf
// ans=""
// for b in range(1,int(n+1)):
//     a=floor((x*b)/y)
//     z=abs(x/y-a/b)
//     if z<m-1e-15:
//         m=z
//         ans=str(a)+'/'+str(b)
//     a=ceil((x*b)/y)
//     z=abs(x/y-a/b)
//     if z<m-1e-15:
//         m=z
//         ans=str(a)+'/'+str(b)
// print(ans)
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

method Solve(v_0: int, v_1: int, v_2: int)
    returns (output: string, ghost steps: nat)
  requires v_1 >= 1
  requires v_2 >= 1
  ensures steps <= v_2 * Kc(v_0, v_2) + 1
{
  steps := 0;
  var x := v_0;
  var y := v_1;
  var n := v_2;
  var hasAns := false;
  var mNum := 0;
  var mDen := 1;
  var ans := "";
  var b := 1;
  ghost var K := Kc(x, n);
  while b <= n
    invariant 1 <= b <= n + 1
    invariant steps <= (b - 1) * K
    decreases n - b
  {
    ghost var s0 := steps;
    IntToStringDigits(b);
    DigitsMono(b, n);
    steps := steps + 2;
    steps := steps + (1 + 1);
    var a1 := FloorDiv(x * b, y);
    ProdBnd(x, b, n);
    DivBnd(x * b, y, 0, AbsInt(x) * n);
    DigitsAbs(a1, AbsInt(x) * n);
    steps := steps + (3 + 1);
    var z1n := AbsInt(x * b - a1 * y);
    steps := steps + 1;
    var z1d := y * b;
    steps := steps + (2 + if !hasAns then 0 else 3);
    if !hasAns || z1n * mDen < mNum * z1d {
      hasAns := true;
      mNum := z1n;
      mDen := z1d;
      steps := steps + (Digits(a1) + |"/"| + Digits(b) + |IntToString(b)|);
      ans := IntToString(a1) + "/" + IntToString(b);
    }
    steps := steps + (3 + 1);
    var a2 := FloorDiv(x * b + y - 1, y);
    DivBnd(x * b, y, y - 1, AbsInt(x) * n);
    assert x * b + (y - 1) == x * b + y - 1;
    DigitsAbs(a2, AbsInt(x) * n);
    steps := steps + (3 + 1);
    var z2n := AbsInt(x * b - a2 * y);
    steps := steps + 1;
    var z2d := y * b;
    steps := steps + (2 + if !hasAns then 0 else 3);
    if !hasAns || z2n * mDen < mNum * z2d {
      hasAns := true;
      mNum := z2n;
      mDen := z2d;
      steps := steps + (Digits(a2) + |"/"| + Digits(b) + |IntToString(b)|);
      ans := IntToString(a2) + "/" + IntToString(b);
    }
    steps := steps + 1;
    assert steps <= s0 + K;
    CostMulDistrib(b - 1, 1, b, K);
    b := b + 1;
  }
  steps := steps + 1;
  output := ans;
}

import opened Prelude

ghost function Kc(x: int, n: int): nat
{
  33 + 2 * Digits(AbsInt(x) * n) + 4 * Digits(n)
}

lemma MulGe(y: int, t: int)
  requires y >= 1 && t >= 0
  ensures y * t >= t
{
  CostMulMonoLeft(1, y, t);
}

lemma ProdBnd(x: int, b: int, n: int)
  requires 1 <= b <= n
  ensures -(AbsInt(x) * n) <= x * b <= AbsInt(x) * n
{
  if x >= 0 {
    CostMulMono(x, b, n);
  } else {
    CostMulMono(-x, b, n);
    assert (-x) * b == -(x * b);
  }
}

lemma DivBnd(p: int, y: int, c: int, M: int)
  requires y >= 1 && 0 <= c < y && M >= 0
  requires -M <= p <= M
  ensures -M <= FloorDiv(p + c, y) <= M
{
  var q := (p + c) / y;
  var r := (p + c) % y;
  assert p + c == y * q + r;
  assert 0 <= r < y;
  if q > M {
    MulGe(y, q - 1);
    assert y * (q - 1) == y * q - y;
  }
  if q < -M {
    MulGe(y, -(q + 1));
    assert y * (-(q + 1)) == -(y * q) - y;
  }
}

lemma DigitsAbs(a: int, M: int)
  requires M >= 0 && -M <= a <= M
  ensures Digits(a) <= Digits(M) + 1
{
  if a >= 0 {
    DigitsMono(a, M);
  } else {
    DigitsMono(-a, M);
  }
}
