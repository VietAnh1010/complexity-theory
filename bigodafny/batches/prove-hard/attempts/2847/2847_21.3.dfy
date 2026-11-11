// --- Python ---------------------------------------------------------
// x, y = map(int, input().split())
//
// cur_x, cur_y = 0, 0
// i = 1
// pos = 0
// sign = [(1, 0), (0, 1), (-1, 0), (0, -1)]
// ans = 0
// j = 0
// while cur_x != x or cur_y != y:
//      if j == i:
//           j = 0
//           if pos % 2 == 1:
//                i += 1
//           pos = (pos + 1) % 4
//           ans += 1
//
//      cur_x = cur_x + sign[pos][0]
//      cur_y = cur_y + sign[pos][1]
//      j += 1
//
// print(ans)
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

// Segment k has length k/2+1 and direction k%4 (0 right, 1 up, 2 left, 3 down).
ghost function SpL(k: nat): nat { k / 2 + 1 }

ghost function {:opaque} SpSt(k: nat): nat
  decreases k
{ if k == 0 then 0 else SpSt(k - 1) + SpL(k - 1) }

ghost function SpDx(k: nat): int
{ if k % 4 == 0 then SpL(k) else if k % 4 == 2 then 0 - SpL(k) else 0 }

ghost function SpDy(k: nat): int
{ if k % 4 == 1 then SpL(k) else if k % 4 == 3 then 0 - SpL(k) else 0 }

ghost function {:opaque} SpCX(k: nat): int
  decreases k
{ if k == 0 then 0 else SpCX(k - 1) + SpDx(k - 1) }

ghost function {:opaque} SpCY(k: nat): int
  decreases k
{ if k == 0 then 0 else SpCY(k - 1) + SpDy(k - 1) }

ghost function SpEx(k: nat, j: nat): int
{ if k % 4 == 0 then j else if k % 4 == 2 then 0 - j else 0 }

ghost function SpEy(k: nat, j: nat): int
{ if k % 4 == 1 then j else if k % 4 == 3 then 0 - j else 0 }

ghost function SpPx(k: nat, j: nat): int { SpCX(k) + SpEx(k, j) }
ghost function SpPy(k: nat, j: nat): int { SpCY(k) + SpEy(k, j) }

ghost function SpAbs(v: int): nat { if v < 0 then -v else v }
ghost function SpMb(a: int, b: int): nat { 4 * (SpAbs(a) + SpAbs(b) + 1) + 4 }
ghost function SpMx(a: int, b: int): int { if a > b then a else b }

lemma SpStep(k: nat)
  ensures SpSt(k + 1) == SpSt(k) + SpL(k)
  ensures SpCX(k + 1) == SpCX(k) + SpDx(k)
  ensures SpCY(k + 1) == SpCY(k) + SpDy(k)
{
  reveal SpSt();
  reveal SpCX();
  reveal SpCY();
}

lemma SpZero()
  ensures SpSt(0) == 0 && SpCX(0) == 0 && SpCY(0) == 0
{
  reveal SpSt();
  reveal SpCX();
  reveal SpCY();
}

lemma SpStMono(k: nat, m: nat)
  requires k <= m
  ensures SpSt(k) <= SpSt(m)
  decreases m - k
{
  if k < m {
    SpStep(m - 1);
    SpStMono(k, m - 1);
  }
}

lemma SpCornerEnd(k: nat)
  ensures SpPx(k, SpL(k)) == SpPx(k + 1, 0)
  ensures SpPy(k, SpL(k)) == SpPy(k + 1, 0)
{ SpStep(k); }

lemma SpAtTarget(k: nat, j: nat, K: nat, J: nat)
  requires j <= SpL(k) && J < SpL(K)
  requires SpSt(k) + j == SpSt(K) + J
  ensures SpPx(k, j) == SpPx(K, J) && SpPy(k, j) == SpPy(K, J)
{
  SpStep(k);
  SpStep(k + 1);
  SpStep(K);
  if j < SpL(k) {
    if k < K { SpStMono(k + 1, K); }
    else if K < k { SpStMono(K + 1, k); }
  } else {
    SpCornerEnd(k);
    if k + 1 < K { SpStMono(k + 2, K); }
    else if K < k + 1 { SpStMono(K + 1, k + 1); }
  }
}

lemma SpCorners(c: nat)
  ensures SpCX(4 * c) == 0 - c && SpCY(4 * c) == 0 - c
  ensures SpCX(4 * c + 1) == c + 1 && SpCY(4 * c + 1) == 0 - c
  ensures SpCX(4 * c + 2) == c + 1 && SpCY(4 * c + 2) == c + 1
  ensures SpCX(4 * c + 3) == 0 - c - 1 && SpCY(4 * c + 3) == c + 1
{
  SpZero();
  if c > 0 {
    SpCorners(c - 1);
    SpStep(4 * c - 1);
  }
  SpStep(4 * c);
  SpStep(4 * c + 1);
  SpStep(4 * c + 2);
}

lemma SpFind(x: int, y: int) returns (K: nat, J: nat)
  ensures J < SpL(K)
  ensures SpPx(K, J) == x && SpPy(K, J) == y
  ensures K + 1 <= SpMb(x, y)
{
  var C: nat := SpMx(SpMx(SpMx(SpMx(0, x - 1), 0 - x - 1), 0 - y), y - 1);
  assert C == 0 || C == x - 1 || C == 0 - x - 1 || C == 0 - y || C == y - 1;
  assert x - 1 <= C && 0 - x - 1 <= C && 0 - y <= C && y - 1 <= C;
  SpCorners(C);
  if x == C + 1 && y <= C {
    K := 4 * C + 1; J := y + C;
  } else if y == C + 1 {
    if x == 0 - C - 1 { K := 4 * C + 3; J := 0; }
    else { K := 4 * C + 2; J := C + 1 - x; }
  } else if x == 0 - C - 1 {
    K := 4 * C + 3; J := C + 1 - y;
  } else {
    assert y == 0 - C;
    K := 4 * C; J := x + C;
  }
}

lemma SpMove(k: nat, j: nat)
  ensures SpPx(k, j + 1) == SpPx(k, j) + (if k % 4 == 0 then 1 else if k % 4 == 2 then -1 else 0)
  ensures SpPy(k, j + 1) == SpPy(k, j) + (if k % 4 == 1 then 1 else if k % 4 == 3 then -1 else 0)
{}

lemma SpQuadStep(k: nat)
  ensures (k + 1) * (k + 1) == k * k + 2 * k + 1
{}

lemma SpStQuad(k: nat)
  ensures 2 * SpSt(k) <= k * k + 2 * k
{
  SpZero();
  if k > 0 {
    SpStQuad(k - 1);
    SpStep(k - 1);
    SpQuadStep(k - 1);
  }
}

method Solve(a: int, b: int)
    returns (output: string, ghost steps: nat)
  ensures steps <= 11 + 8 * (SpMb(a, b) * SpMb(a, b) + 2 * SpMb(a, b)) + |output|
{
  steps := 0;
  var x := a;
  var y := b;
  var curX := 0;
  var curY := 0;
  var i := 1;
  var pos := 0;
  steps := steps + 4;
  var signX := [1, 0, -1, 0];
  steps := steps + 4;
  var signY := [0, 1, 0, -1];
  var ans := 0;
  var j := 0;
  assert signX[0] == 1 && signX[1] == 0 && signX[2] == -1 && signX[3] == 0;
  assert signY[0] == 0 && signY[1] == 1 && signY[2] == 0 && signY[3] == -1;
  SpZero();
  ghost var K: nat, J: nat := SpFind(x, y);
  ghost var TT: nat := SpSt(K) + J;
  ghost var k: nat := 0;
  while curX != x || curY != y
    invariant 0 <= pos < 4
    invariant pos == k % 4
    invariant i == SpL(k)
    invariant 0 <= j <= i
    invariant curX == SpPx(k, j) && curY == SpPy(k, j)
    invariant steps <= 8 + 16 * (SpSt(k) + j)
    invariant SpSt(k) + j <= TT
    decreases TT - (SpSt(k) + j)
  {
    if SpSt(k) + j == TT { SpAtTarget(k, j, K, J); }
    assert SpSt(k) + j < TT;
    steps := steps + (3 + if curX != x then 0 else 1);
    steps := steps + 1;
    if j == i {
      SpStep(k);
      SpCornerEnd(k);
      j := 0;
      steps := steps + 2;
      if pos % 2 == 1 {
        steps := steps + 1;
        i := i + 1;
      }
      steps := steps + 2;
      pos := (pos + 1) % 4;
      steps := steps + 1;
      ans := ans + 1;
      k := k + 1;
    }
    assert curX == SpPx(k, j) && curY == SpPy(k, j) && pos == k % 4;
    SpMove(k, j);
    if pos == 0 { assert signX[pos] == 1 && signY[pos] == 0; }
    else if pos == 1 { assert signX[pos] == 0 && signY[pos] == 1; }
    else if pos == 2 { assert signX[pos] == -1 && signY[pos] == 0; }
    else { assert signX[pos] == 0 && signY[pos] == -1; }
    steps := steps + 2;
    curX := curX + signX[pos];
    steps := steps + 2;
    curY := curY + signY[pos];
    steps := steps + 1;
    j := j + 1;
  }
  steps := steps + (2 + if curX != x then 0 else 1);
  steps := steps + Digits(ans);
  output := IntToString(ans);
  IntToStringDigits(ans);
  ghost var M: nat := SpMb(a, b);
  SpStep(K);
  SpStMono(K + 1, M);
  SpStQuad(M);
}

import opened Prelude
