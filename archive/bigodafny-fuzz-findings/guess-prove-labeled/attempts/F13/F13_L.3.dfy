// --- Python ---------------------------------------------------------
// def walk(mirror, p):
//     n = len(mirror)
//     d = 1
//     while 0 <= p < n:
//         if mirror[p] == 1:
//             d = -d
//         mirror[p] = 1 - mirror[p]
//         p += d
//     return p
//
// n = int(input())
// a = list(map(int, input().split()))
// mirror = [0] * n
// right = 0
// for i in range(n):
//     for _ in range(a[i]):
//         if walk(mirror, i) == n:
//             right += 1
// print(right, mirror.count(1))
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

ghost function Pow5(k: nat): nat
  ensures Pow5(k) >= 1
  decreases k
{
  if k == 0 then 1 else 5 * Pow5(k - 1)
}

// base-5 digit of cell j: a lexicographic potential, cell 0 most significant
ghost function Dig(b: seq<int>, p: int, d: int, j: int): nat
  requires 0 <= j < |b|
  ensures Dig(b, p, d, j) <= 4
{
  if j < p then (if b[j] == 0 then 1 else 3)
  else if j == p then (if d > 0 then 4 else if b[j] == 0 then 0 else 2)
  else 0
}

ghost function Val(b: seq<int>, p: int, d: int, k: nat): nat
  requires k <= |b|
  decreases k
{
  if k == 0 then 0 else Val(b, p, d, k - 1) * 5 + Dig(b, p, d, k - 1)
}

ghost function Meas(b: seq<int>, p: int, d: int): nat
{
  Val(b, p, d, |b|) + (if 0 <= p < |b| then 1 else 0)
}

lemma ValBound(b: seq<int>, p: int, d: int, k: nat)
  requires k <= |b|
  ensures Val(b, p, d, k) < Pow5(k)
  decreases k
{
  if k > 0 { ValBound(b, p, d, k - 1); }
}

lemma ValZero(b: seq<int>, p: int, d: int, k: nat)
  requires k <= |b|
  requires p < 0
  ensures Val(b, p, d, k) == 0
  decreases k
{
  if k > 0 { ValZero(b, p, d, k - 1); }
}

lemma ValEq(b: seq<int>, p: int, d: int, b2: seq<int>, p2: int, d2: int, k: nat)
  requires k <= |b| && k <= |b2|
  requires forall i :: 0 <= i < k ==> Dig(b, p, d, i) == Dig(b2, p2, d2, i)
  ensures Val(b, p, d, k) == Val(b2, p2, d2, k)
  decreases k
{
  if k > 0 { ValEq(b, p, d, b2, p2, d2, k - 1); }
}

lemma LexLess(b: seq<int>, p: int, d: int, b2: seq<int>, p2: int, d2: int, j: nat, k: nat)
  requires j < k <= |b| && k <= |b2|
  requires forall i :: 0 <= i < j ==> Dig(b, p, d, i) == Dig(b2, p2, d2, i)
  requires Dig(b, p, d, j) < Dig(b2, p2, d2, j)
  ensures Val(b, p, d, k) < Val(b2, p2, d2, k)
  decreases k
{
  if k == j + 1 {
    ValEq(b, p, d, b2, p2, d2, j);
  } else {
    LexLess(b, p, d, b2, p2, d2, j, k - 1);
  }
}

lemma StepDecr(b0: seq<int>, p0: int, d0: int, b1: seq<int>, p1: int, d1: int)
  requires |b0| == |b1|
  requires 0 <= p0 < |b0|
  requires forall i :: 0 <= i < |b0| ==> b0[i] == 0 || b0[i] == 1
  requires d0 == 1 || d0 == -1
  requires b1[p0] == 1 - b0[p0]
  requires forall i :: 0 <= i < |b0| && i != p0 ==> b1[i] == b0[i]
  requires d1 == (if b0[p0] == 1 then -d0 else d0)
  requires p1 == p0 + d1
  ensures Meas(b1, p1, d1) < Meas(b0, p0, d0)
{
  var n := |b0|;
  if p1 == p0 + 1 {
    assert Dig(b1, p1, d1, p0) < Dig(b0, p0, d0, p0);
    LexLess(b1, p1, d1, b0, p0, d0, p0, n);
  } else if p0 >= 1 {
    assert Dig(b1, p1, d1, p0 - 1) < Dig(b0, p0, d0, p0 - 1);
    LexLess(b1, p1, d1, b0, p0, d0, p0 - 1, n);
  } else {
    ValZero(b1, p1, d1, n);
  }
}

ghost function Qc(n: nat): nat { 11 * Pow5(n) + 10 }
ghost function Kc(n: nat): nat { 3 * Qc(n) + 5 }

method Walk(mirror: array<int>, start: int)
    returns (p: int, ghost steps: nat)
  requires forall i :: 0 <= i < mirror.Length ==> mirror[i] == 0 || mirror[i] == 1
  ensures forall i :: 0 <= i < mirror.Length ==> mirror[i] == 0 || mirror[i] == 1
  ensures steps <= 11 * Pow5(mirror.Length) + 4
  modifies mirror
{
  steps := 0;
  steps := steps + 1;
  var n := mirror.Length;
  var d := 1;
  p := start;
  ghost var m0 := Meas(mirror[..], start, 1);
  ValBound(mirror[..], start, 1, n);
  while 0 <= p < n
    invariant forall i :: 0 <= i < n ==> mirror[i] == 0 || mirror[i] == 1
    invariant d == 1 || d == -1
    invariant steps + 11 * Meas(mirror[..], p, d) <= 1 + 11 * m0
    decreases Meas(mirror[..], p, d)
  {
    ghost var b0 := mirror[..];
    ghost var p0 := p;
    ghost var d0 := d;
    steps := steps + 4;
    steps := steps + 2;
    if mirror[p] == 1 {
      steps := steps + 1;
      d := -d;
    }
    steps := steps + 3;
    mirror[p] := 1 - mirror[p];
    steps := steps + 1;
    p := p + d;
    StepDecr(b0, p0, d0, mirror[..], p, d);
  }
  steps := steps + 3;
}

method Solve(n: int, a_list: seq<int>)
    returns (output: string, ghost steps: nat)
  requires n >= 1 && |a_list| == n
  requires forall i :: 0 <= i < n ==> 0 <= a_list[i] <= 3
  ensures steps <= n * Kc(n) + 11 * n + 2 + 2 * |output|
{
  steps := 0;
  steps := steps + n;
  var mirror := new int[n];
  var k := 0;
  while k < n
    invariant 0 <= k <= n
    invariant forall j :: 0 <= j < k ==> mirror[j] == 0
    invariant steps <= n + 4 * k
    decreases n - k
  {
    steps := steps + 2;
    steps := steps + 1;
    mirror[k] := 0;
    steps := steps + 1;
    k := k + 1;
  }
  steps := steps + 1;
  var right := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < n ==> mirror[j] == 0 || mirror[j] == 1
    invariant steps <= 5 * n + 1 + i * Kc(n)
    decreases n - i
  {
    CostMulDistrib(i, 1, i + 1, Kc(n));
    steps := steps + 2;
    var t := 0;
    ghost var s1 := steps;
    while t < a_list[i]
      invariant 0 <= t <= a_list[i]
      invariant forall j :: 0 <= j < n ==> mirror[j] == 0 || mirror[j] == 1
      invariant steps <= s1 + t * Qc(n)
      decreases a_list[i] - t
    {
      CostMulDistrib(t, 1, t + 1, Qc(n));
      steps := steps + 3;
      var p, s0 := Walk(mirror, i);
      steps := steps + s0;
      steps := steps + 1;
      if p == n {
        steps := steps + 1;
        right := right + 1;
      }
      steps := steps + 1;
      t := t + 1;
    }
    CostMulMonoLeft(t, 3, Qc(n));
    steps := steps + 2;
    steps := steps + 1;
    i := i + 1;
  }
  steps := steps + 1;
  var up := 0;
  k := 0;
  ghost var s3 := steps;
  while k < n
    invariant 0 <= k <= n
    invariant steps <= s3 + 6 * k
    decreases n - k
  {
    steps := steps + 2;
    steps := steps + 2;
    if mirror[k] == 1 {
      steps := steps + 1;
      up := up + 1;
    }
    steps := steps + 1;
    k := k + 1;
  }
  steps := steps + 1;
  IntToStringDigits(right);
  IntToStringDigits(up);
  steps := steps + (Digits(right) + |" "| + Digits(up) + |IntToString(up)|);
  output := IntToString(right) + " " + IntToString(up);
}

import opened Prelude
