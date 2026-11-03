// 281_B. Nearest Fraction  (problem 696, solution 696_51)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
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

ghost function Wb(x: int, y: int, n: int): nat
  requires y >= 1 && n >= 1
{
  AbsInt(x) * n + y + n + 1
}

lemma DivBound(p: int, y: int)
  requires y >= 1
  ensures AbsInt(FloorDiv(p, y)) <= AbsInt(p) + 1
{
  var q := p / y;
  var r := p % y;
  assert p == y * q + r && 0 <= r < y;
  if p >= 0 {
    assert q >= 0;
    CostMulMono(q as nat, 1, y as nat);
    assert q * y == y * q;
  } else if q < 0 {
    var m := -q - 1;
    assert m >= 0;
    CostMulMono(m as nat, 1, y as nat);
    assert m * y == -(q * y) - y;
    assert q * y == y * q;
  }
}

lemma XB(x: int, b: int, n: int)
  requires 1 <= b <= n
  ensures AbsInt(x * b) <= AbsInt(x) * n
{
  if x >= 0 {
    CostMulMono(x as nat, b as nat, n as nat);
  } else {
    CostMulMono((-x) as nat, b as nat, n as nat);
  }
}

lemma DigitsBound(a: int, W: nat)
  requires AbsInt(a) <= W
  ensures Digits(a) <= 1 + Digits(W)
{
  if a < 0 { DigitsMono(-a, W); } else { DigitsMono(a, W); }
}


method Solve(v_0: int, v_1: int, v_2: int)
    returns (output: string, ghost steps: nat)
  requires v_1 >= 1
  requires v_2 >= 1
  ensures steps <= 1 + v_2 * (6 * Digits(Wb(v_0, v_1, v_2)) + 40)
{
  steps := 0;
  var x := v_0;
  var y := v_1;
  var n := v_2;
  ghost var D := Digits(Wb(x, y, n));
  ghost var K := 6 * D + 40;
  var hasAns := false;
  var mNum := 0;
  var mDen := 1;
  var ans := "";
  var b := 1;
  while b <= n
    invariant 1 <= b <= n + 1
    invariant steps <= (b - 1) * K
    decreases n - b
  {
    XB(x, b, n);
    DivBound(x * b, y);
    DivBound(x * b + y - 1, y);
    CostMulDistrib(b - 1, 1, b, K);
    steps := steps + 2;
    steps := steps + (1 + 1);
    var a1 := FloorDiv(x * b, y);
    steps := steps + (3 + 1);
    var z1n := AbsInt(x * b - a1 * y);
    steps := steps + 1;
    var z1d := y * b;
    steps := steps + (2 + if !hasAns then 0 else 3);
    if !hasAns || z1n * mDen < mNum * z1d {
      hasAns := true;
      mNum := z1n;
      mDen := z1d;
      DigitsBound(a1, Wb(x, y, n));
      DigitsBound(b, Wb(x, y, n));
      IntToStringDigits(b);
      steps := steps + (Digits(a1) + |"/"| + Digits(b) + |IntToString(b)|);
      ans := IntToString(a1) + "/" + IntToString(b);
    }
    steps := steps + (3 + 1);
    var a2 := FloorDiv(x * b + y - 1, y);
    steps := steps + (3 + 1);
    var z2n := AbsInt(x * b - a2 * y);
    steps := steps + 1;
    var z2d := y * b;
    steps := steps + (2 + if !hasAns then 0 else 3);
    if !hasAns || z2n * mDen < mNum * z2d {
      hasAns := true;
      mNum := z2n;
      mDen := z2d;
      DigitsBound(a2, Wb(x, y, n));
      DigitsBound(b, Wb(x, y, n));
      IntToStringDigits(b);
      steps := steps + (Digits(a2) + |"/"| + Digits(b) + |IntToString(b)|);
      ans := IntToString(a2) + "/" + IntToString(b);
    }
    steps := steps + 1;
    b := b + 1;
  }
  steps := steps + 1;
  output := ans;
}

import opened Prelude
