// --- Python ---------------------------------------------------------
// def walk(mark, p):
//     n = len(mark)
//     d = 1
//     while 0 <= p < n:
//         bounce = mark[p] == 1
//         mark[p] = 1 if d == -1 else 0
//         if bounce:
//             d = -d
//         p += d
//     return p
//
// n = int(input())
// a = list(map(int, input().split()))
// mark = [1] * n
// right = 0
// for i in range(n):
//     for _ in range(a[i]):
//         if walk(mark, i) == n:
//             right += 1
// print(right, mark.count(1))
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

ghost function Pow(k: nat): nat
{
  if k == 0 then 1 else 2 * Pow(k - 1)
}

lemma PowMono(a: nat, b: nat)
  requires a <= b
  ensures Pow(a) <= Pow(b)
  decreases b
{
  if a < b { PowMono(a, b - 1); }
}

lemma PowGt(k: nat)
  ensures k + 1 <= Pow(k)
{
  if k > 0 { PowGt(k - 1); }
}

// cost of a run of k ones between a wall and the ball
ghost function U(k: nat): nat
{
  if k == 0 then 0 else 2 * U(k - 1) + k + 2
}

lemma UClosed(k: nat)
  ensures U(k) + k + 4 == 4 * Pow(k)
{
  if k > 0 { UClosed(k - 1); }
}

ghost function Cost(q: int, r: int): nat
  requires r < q
{
  (q - r + 2) + U(q - 1 - r)
}

lemma CostLe(q: nat, r: int)
  requires -1 <= r < q
  ensures Cost(q, r) <= 8 * Pow(q)
  ensures 1 <= 8 * Pow(q)
{
  PowGt(q);
  UClosed(q - 1 - r);
  PowMono(q - 1 - r, q);
}

ghost function Tail(m: seq<int>, q: nat, r: int, v: int): nat
  requires r < q
  decreases |m| - q
{
  if q >= |m| then 0
  else (if q <= v || m[q] == 1 then Cost(q, r) else 1) + Tail(m, q + 1, r, v)
}

// nearest index below p holding a 1, or -1
ghost function Wall(m: seq<int>, p: nat): int
  requires p <= |m|
  ensures -1 <= Wall(m, p) < p
  decreases p
{
  if p == 0 then -1 else if m[p - 1] == 1 then p - 1 else Wall(m, p - 1)
}

ghost function PhiR(m: seq<int>, p: nat): nat
  requires p < |m|
{
  Tail(m, p, Wall(m, p), -1)
}

ghost function PhiL(m: seq<int>, p: nat): nat
  requires p < |m|
{
  var r := Wall(m, p + 1);
  if r < 0 then p + 1 else (p - r) + 1 + Tail(m, r + 1, r, p)
}

ghost function Phi(m: seq<int>, p: int, d: int): nat
{
  if p < 0 || p >= |m| then 0
  else if d == 1 then PhiR(m, p) else PhiL(m, p)
}

lemma WallSame(m1: seq<int>, m2: seq<int>, p: nat)
  requires |m1| == |m2|
  requires p <= |m1|
  requires forall i :: 0 <= i < p ==> m1[i] == m2[i]
  ensures Wall(m1, p) == Wall(m2, p)
  decreases p
{
  if p > 0 { WallSame(m1, m2, p - 1); }
}

lemma TailAgree(m1: seq<int>, m2: seq<int>, q: nat, r: int, v1: int, v2: int)
  requires |m1| == |m2|
  requires r < q
  requires v1 < q && v2 < q
  requires forall i :: q <= i < |m1| ==> m1[i] == m2[i]
  ensures Tail(m1, q, r, v1) == Tail(m2, q, r, v2)
  decreases |m1| - q
{
  if q < |m1| { TailAgree(m1, m2, q + 1, r, v1, v2); }
}

lemma TailAbs(m: seq<int>, p: nat, q: nat, r: int)
  requires p < |m|
  requires r < q
  ensures Tail(m[p := 1], q, r, p - 1) == Tail(m, q, r, p)
  decreases |m| - q
{
  if q < |m| {
    TailAbs(m, p, q + 1, r);
    assert (q <= p - 1 || m[p := 1][q] == 1) == (q <= p || m[q] == 1);
  }
}

lemma Run(m: seq<int>, r: int, q: nat, v: int)
  requires r < q
  requires q <= v + 1
  requires v < |m|
  ensures Tail(m, q, r, v) + U(q - 1 - r) == U(v - r) + Tail(m, v + 1, r, v)
  decreases v + 1 - q
{
  if q <= v {
    Run(m, r, q + 1, v);
    assert Tail(m, q, r, v) == Cost(q, r) + Tail(m, q + 1, r, v);
    assert U(q - r) == 2 * U(q - 1 - r) + (q - r) + 2;
  }
}

lemma TailBound(m: seq<int>, q: nat, r: int, v: int)
  requires -1 <= r < q
  requires q <= |m|
  ensures Tail(m, q, r, v) + 8 * Pow(q) <= 8 * Pow(|m|)
  decreases |m| - q
{
  if q < |m| {
    TailBound(m, q + 1, r, v);
    CostLe(q, r);
    assert Pow(q + 1) == 2 * Pow(q);
  }
}

lemma PhiBound(m: seq<int>, p: int, d: int)
  ensures Phi(m, p, d) <= 9 * Pow(|m|)
{
  if 0 <= p < |m| {
    var n := |m|;
    PowGt(n);
    if d == 1 {
      TailBound(m, p, Wall(m, p), -1);
    } else {
      var r := Wall(m, p + 1);
      if r >= 0 { TailBound(m, r + 1, r, p); }
    }
  }
}

lemma StepPhi(m: seq<int>, p: int, d: int, m2: seq<int>, p2: int, d2: int)
  requires 0 <= p < |m|
  requires d == 1 || d == -1
  requires m[p] == 0 || m[p] == 1
  requires m2 == m[p := (if d == -1 then 1 else 0)]
  requires d2 == (if m[p] == 1 then -d else d)
  requires p2 == p + d2
  ensures Phi(m2, p2, d2) + 1 <= Phi(m, p, d)
{
  var r := Wall(m, p);
  assert |m2| == |m|;
  if d == 1 {
    assert Phi(m, p, d) == Tail(m, p, r, -1);
    if m[p] == 0 {
      assert m2 == m;
      assert Tail(m, p, r, -1) == 1 + Tail(m, p + 1, r, -1);
      if p + 1 < |m| {
        assert Wall(m, p + 1) == r;
        assert Phi(m2, p2, d2) == Tail(m, p + 1, r, -1);
      }
    } else {
      assert Tail(m, p, r, -1) == Cost(p, r) + Tail(m, p + 1, r, -1);
      if p >= 1 {
        WallSame(m, m2, p);
        assert Wall(m2, p) == r;
        if r >= 0 {
          Run(m2, r, r + 1, p - 1);
          TailAgree(m2, m, p + 1, r, p - 1, -1);
          assert Tail(m2, p, r, p - 1) == 1 + Tail(m2, p + 1, r, p - 1);
          assert U(0) == 0;
          assert Phi(m2, p2, d2) == (p - 1 - r) + 1 + Tail(m2, r + 1, r, p - 1);
        }
      }
    }
  } else {
    assert Phi(m, p, d) == PhiL(m, p);
    if m[p] == 0 {
      assert Wall(m, p + 1) == r;
      if p >= 1 {
        WallSame(m, m2, p);
        assert Wall(m2, p) == r;
        if r >= 0 { TailAbs(m, p, r + 1, r); }
      }
    } else {
      assert m2 == m;
      assert Wall(m, p + 1) == p;
      if p + 1 < |m| {
        TailAgree(m, m, p + 1, p, p, -1);
      }
    }
  }
}

method Walk(mark: array<int>, start: int)
    returns (p: int, ghost steps: nat)
  requires forall i :: 0 <= i < mark.Length ==> mark[i] == 0 || mark[i] == 1
  ensures forall i :: 0 <= i < mark.Length ==> mark[i] == 0 || mark[i] == 1
  ensures steps <= 90 * Pow(mark.Length) + 4
  modifies mark
{
  steps := 0;
  steps := steps + 1;
  var n := mark.Length;
  var d := 1;
  p := start;
  ghost var phi0 := Phi(mark[..], p, d);
  PhiBound(mark[..], p, d);
  while 0 <= p < n
    invariant n == mark.Length
    invariant d == 1 || d == -1
    invariant forall i :: 0 <= i < n ==> mark[i] == 0 || mark[i] == 1
    invariant d == -1 ==> -1 <= p < n
    invariant steps + 10 * Phi(mark[..], p, d) <= 10 * phi0 + 1
    decreases Phi(mark[..], p, d)
  {
    ghost var m0 := mark[..];
    ghost var p0 := p;
    ghost var d0 := d;
    ghost var s0 := steps;
    steps := steps + 4;
    steps := steps + 2;
    var bounce := mark[p] == 1;
    steps := steps + 1;
    if d == -1 {
      steps := steps + 1;
      mark[p] := 1;
    } else {
      steps := steps + 1;
      mark[p] := 0;
    }
    if bounce {
      steps := steps + 1;
      d := -d;
    }
    steps := steps + 1;
    p := p + d;
    assert mark[..] == m0[p0 := (if d0 == -1 then 1 else 0)];
    StepPhi(m0, p0, d0, mark[..], p, d);
    assert steps <= s0 + 10;
  }
  steps := steps + 3;
}

method Solve(n: int, a_list: seq<int>)
    returns (output: string, ghost steps: nat)
  requires n >= 1 && |a_list| == n
  requires forall i :: 0 <= i < n ==> 0 <= a_list[i] <= 3
  ensures steps <= n * (290 * Pow(n)) + 11 * n + 3 + 2 * |output|
{
  steps := 0;
  ghost var P := Pow(n);
  PowGt(n);
  ghost var K1 := 95 * P;
  ghost var K2 := 290 * P;
  steps := steps + n;
  var mark := new int[n];
  var k := 0;
  while k < n
    invariant 0 <= k <= n
    invariant mark.Length == n
    invariant forall j :: 0 <= j < k ==> mark[j] == 1
    invariant steps == n + 4 * k
    decreases n - k
  {
    steps := steps + 2;
    steps := steps + 1;
    mark[k] := 1;
    steps := steps + 1;
    k := k + 1;
  }
  steps := steps + 1;
  var right := 0;
  var i := 0;
  ghost var s1 := steps;
  while i < n
    invariant 0 <= i <= n
    invariant mark.Length == n
    invariant forall j :: 0 <= j < n ==> mark[j] == 0 || mark[j] == 1
    invariant steps <= s1 + i * K2
    decreases n - i
  {
    steps := steps + 2;
    var t := 0;
    ghost var sb := steps;
    while t < a_list[i]
      invariant 0 <= t <= a_list[i]
      invariant mark.Length == n
      invariant forall j :: 0 <= j < n ==> mark[j] == 0 || mark[j] == 1
      invariant steps <= sb + t * K1
      decreases a_list[i] - t
    {
      steps := steps + 3;
      var p, s0 := Walk(mark, i);
      steps := steps + s0;
      steps := steps + 1;
      if p == n {
        steps := steps + 1;
        right := right + 1;
      }
      steps := steps + 1;
      CostMulDistrib(t, 1, t + 1, K1);
      t := t + 1;
    }
    CostMulMonoLeft(t, 3, K1);
    steps := steps + 2;
    steps := steps + 1;
    CostMulDistrib(i, 1, i + 1, K2);
    i := i + 1;
  }
  steps := steps + 1;
  var up := 0;
  k := 0;
  ghost var s2 := steps;
  while k < n
    invariant 0 <= k <= n
    invariant mark.Length == n
    invariant steps <= s2 + 6 * k
    decreases n - k
  {
    steps := steps + 2;
    steps := steps + 2;
    if mark[k] == 1 {
      steps := steps + 1;
      up := up + 1;
    }
    steps := steps + 1;
    k := k + 1;
  }
  steps := steps + 1;
  steps := steps + (Digits(right) + |" "| + Digits(up) + |IntToString(up)|);
  output := IntToString(right) + " " + IntToString(up);
  IntToStringDigits(right);
  IntToStringDigits(up);
  assert K2 == 290 * Pow(n);
  assert n * K2 == n * (290 * Pow(n));
}

import opened Prelude
