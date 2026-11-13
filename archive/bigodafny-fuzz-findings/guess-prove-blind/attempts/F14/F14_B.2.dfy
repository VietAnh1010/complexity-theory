// --- Python ---------------------------------------------------------
// n = int(input())
// a = list(map(int, input().split()))
// alive = [1] * n
// p = n - 1
// for t in range(n):
//     s = a[t] + 1
//     while s > 0:
//         p = (p + 1) % n
//         if alive[p]:
//             s -= 1
//     alive[p] = 0
// print(p + 1)
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

ghost function Cnt(x: seq<int>): int
  decreases |x|
{
  if |x| == 0 then 0 else x[|x| - 1] + Cnt(x[..|x| - 1])
}

lemma CntOnes(x: seq<int>)
  requires forall i :: 0 <= i < |x| ==> x[i] == 1
  ensures Cnt(x) == |x|
  decreases |x|
{
  if |x| > 0 { CntOnes(x[..|x| - 1]); }
}

lemma CntKill(x: seq<int>, p: int)
  requires 0 <= p < |x|
  requires x[p] == 1
  ensures Cnt(x[p := 0]) == Cnt(x) - 1
  decreases |x|
{
  var y := x[p := 0];
  if p == |x| - 1 {
    assert y[..|y| - 1] == x[..|x| - 1];
  } else {
    assert y[..|y| - 1] == x[..|x| - 1][p := 0];
    CntKill(x[..|x| - 1], p);
  }
}

lemma CntPos(x: seq<int>)
  requires forall i :: 0 <= i < |x| ==> x[i] == 0 || x[i] == 1
  requires Cnt(x) >= 1
  ensures exists q :: 0 <= q < |x| && x[q] == 1
  decreases |x|
{
  if x[|x| - 1] == 1 {
    assert 0 <= |x| - 1 < |x| && x[|x| - 1] == 1;
  } else {
    CntPos(x[..|x| - 1]);
    var q :| 0 <= q < |x| - 1 && x[..|x| - 1][q] == 1;
    assert x[q] == 1;
  }
}

ghost function D(q: int, p: int, n: int): int
  requires n >= 1
{
  if q > p then q - p else q - p + n
}

lemma DStep(q: int, p: int, n: int)
  requires n >= 1 && 0 <= p < n && 0 <= q < n
  ensures 1 <= D(q, p, n) <= n
  ensures D(q, p, n) > 1 ==> (p + 1) % n != q && D(q, (p + 1) % n, n) == D(q, p, n) - 1
  ensures D(q, p, n) == 1 ==> (p + 1) % n == q && D(q, (p + 1) % n, n) == n
{
  if p + 1 < n {
    SmallMod(p + 1, n);
  } else {
    ModUpper(n, n);
  }
}

lemma MulSub(x: int, n: int)
  ensures (x - 1) * n == x * n - n
{
}

lemma MulNonneg(x: int, n: int)
  requires x >= 0 && n >= 0
  ensures x * n >= 0
{
}

lemma MulLe3(x: int, n: int)
  requires 0 <= x <= 3 && n >= 0
  ensures x * n <= 3 * n
{
}

lemma KSquare(n: nat, K: nat)
  requires K == 35 * n + 7
  ensures n * K == 35 * (n * n) + 7 * n
{
}

method Solve(n: int, a_list: seq<int>)
    returns (output: string, ghost steps: nat)
  requires n >= 1 && |a_list| == n
  requires forall i :: 0 <= i < n ==> 0 <= a_list[i] <= 3
  ensures steps <= 35 * (n * n) + 12 * n + 5 + |output|
{
  steps := 0;
  steps := steps + n;
  var alive := new int[n];
  var k := 0;
  while k < n
    invariant 0 <= k <= n
    invariant steps <= n + 4 * k
    invariant forall i :: 0 <= i < k ==> alive[i] == 1
    decreases n - k
  {
    steps := steps + 2;
    steps := steps + 1;
    alive[k] := 1;
    steps := steps + 1;
    k := k + 1;
  }
  CntOnes(alive[..]);
  steps := steps + 1;
  steps := steps + 1;
  var p := n - 1;
  var t := 0;
  ghost var K := 35 * n + 7;
  while t < n
    invariant 0 <= t <= n
    invariant 0 <= p < n
    invariant alive.Length == n
    invariant forall i :: 0 <= i < n ==> alive[i] == 0 || alive[i] == 1
    invariant Cnt(alive[..]) == n - t
    invariant steps <= 5 * n + 2 + t * K
    decreases n - t
  {
    steps := steps + 2;
    steps := steps + 2;
    var s := a_list[t] + 1;
    CntPos(alive[..]);
    ghost var q :| 0 <= q < n && alive[q] == 1;
    ghost var A := alive[..];
    ghost var S0 := steps;
    ghost var it: nat := 0;
    ghost var w: int := a_list[t] * n;
    MulLe3(a_list[t], n);
    DStep(q, p, n);
    while s > 0
      invariant 0 <= s <= 4
      invariant 0 <= p < n
      invariant alive[..] == A
      invariant w == (s - 1) * n
      invariant it + w + D(q, p, n) <= 4 * n
      invariant steps <= S0 + 7 * it
      invariant s == 0 ==> alive[p] == 1
      decreases w + n + D(q, p, n)
    {
      MulNonneg(s, n);
      MulSub(s, n);
      steps := steps + 2;
      steps := steps + 2;
      ghost var p0 := p;
      p := (p + 1) % n;
      DStep(q, p0, n);
      DStep(q, p, n);
      steps := steps + 2;
      if alive[p] == 1 {
        steps := steps + 1;
        s := s - 1;
        w := w - n;
        MulSub(s, n);
      }
      it := it + 1;
    }
    MulNonneg(s, n);
    MulSub(s, n);
    steps := steps + 1;
    steps := steps + 1;
    ghost var A0 := alive[..];
    alive[p] := 0;
    CntKill(A0, p);
    assert alive[..] == A0[p := 0];
    steps := steps + 1;
    t := t + 1;
    CostMulDistrib(t - 1, 1, t, K);
  }
  steps := steps + 1;
  steps := steps + (1 + Digits(p + 1));
  output := IntToString(p + 1);
  IntToStringDigits(p + 1);
  KSquare(n, K);
}

import opened Prelude
