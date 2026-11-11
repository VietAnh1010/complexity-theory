// --- Python ---------------------------------------------------------
// def walk(arrow, p):
//     n = len(arrow)
//     while 0 <= p < n:
//         q = arrow[p]
//         arrow[p] = -q
//         p += q
//     return p
//
// n = int(input())
// a = list(map(int, input().split()))
// arrow = [1] * n
// right = 0
// for i in range(n):
//     for _ in range(a[i]):
//         if walk(arrow, i) == n:
//             right += 1
// print(right, arrow.count(1))
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

// A cell is "toward" the walker at p when its arrow points at p.
ghost predicate IsT(s: seq<int>, p: int, x: int)
{
  0 <= x < |s| && ((x < p && s[x] == 1) || (x > p && s[x] == -1))
}

ghost function TC(s: seq<int>, p: int, i: nat): nat
  requires i <= |s|
  decreases i
{
  if i == 0 then 0 else TC(s, p, i - 1) + (if IsT(s, p, i - 1) then 1 else 0)
}

lemma TCLe(s: seq<int>, p: int, i: nat)
  requires i <= |s|
  ensures TC(s, p, i) <= i
  decreases i
{
  if i > 0 { TCLe(s, p, i - 1); }
}

// Steps from q in direction d until an out-of-range cell or a cell pointing back.
ghost function Run(s: seq<int>, d: int, q: int): nat
  requires d == 1 || d == -1
  ensures Run(s, d, q) >= 1
  decreases if d == 1 then |s| - q else q + 1
{
  if q < 0 || q >= |s| || s[q] == -d then 1 else 1 + Run(s, d, q + d)
}

lemma RunBnd(s: seq<int>, d: int, q: int)
  requires d == 1 || d == -1
  ensures Run(s, d, q) <= (if 0 <= q < |s| then (if d == 1 then |s| - q + 1 else q + 2) else 1)
  ensures Run(s, d, q) <= |s| + 1
  decreases if d == 1 then |s| - q else q + 1
{
  if 0 <= q < |s| && s[q] != -d {
    RunBnd(s, d, q + d);
  }
}

lemma RunSame(s: seq<int>, s2: seq<int>, d: int, q: int, p: int)
  requires d == 1 || d == -1
  requires |s2| == |s|
  requires forall x :: 0 <= x < |s| && x != p ==> s2[x] == s[x]
  requires d == 1 ==> q > p
  requires d == -1 ==> q < p
  ensures Run(s2, d, q) == Run(s, d, q)
  decreases if d == 1 then |s| - q else q + 1
{
  if 0 <= q < |s| && s[q] != -d {
    RunSame(s, s2, d, q + d, p);
  }
}

ghost function Dist(s: seq<int>, p: int): nat
{
  if p < 0 || p >= |s| then 0
  else if s[p] == 1 then Run(s, 1, p + 1)
  else Run(s, -1, p - 1)
}

ghost function PF(s: seq<int>, p: int): nat
{
  if p < 0 || p >= |s| then 0
  else TC(s, p, |s|) * (|s| + 2) + Dist(s, p)
}

lemma PBound(s: seq<int>, p: int)
  ensures PF(s, p) <= |s| * (|s| + 2) + |s| + 1
{
  if 0 <= p < |s| {
    TCLe(s, p, |s|);
    RunBnd(s, 1, p + 1);
    RunBnd(s, -1, p - 1);
    CostMulMonoLeft(TC(s, p, |s|), |s|, |s| + 2);
  }
}

lemma TCStep(s: seq<int>, p: int, i: nat)
  requires 0 <= p < |s|
  requires s[p] == 1 || s[p] == -1
  requires 0 <= p + s[p] < |s|
  requires i <= |s|
  ensures TC(s[p := -s[p]], p + s[p], i)
          + (if p + s[p] < i && s[p + s[p]] == -s[p] then 1 else 0)
          == TC(s, p, i)
  decreases i
{
  if i > 0 { TCStep(s, p, i - 1); }
}

lemma StepP(s: seq<int>, p: int)
  requires 0 <= p < |s|
  requires forall x :: 0 <= x < |s| ==> s[x] == 1 || s[x] == -1
  ensures PF(s[p := -s[p]], p + s[p]) < PF(s, p)
{
  var d := s[p];
  var p2 := p + d;
  var s2 := s[p := -d];
  if 0 <= p2 < |s| {
    TCStep(s, p, |s|);
    var m := |s| + 2;
    if s[p2] == d {
      RunSame(s, s2, d, p2 + d, p);
      assert Dist(s2, p2) + 1 == Dist(s, p);
    } else {
      assert s[p2] == -d;
      assert Dist(s, p) == 1;
      RunBnd(s2, 1, p2 + 1);
      RunBnd(s2, -1, p2 - 1);
      CostMulDistrib(TC(s2, p2, |s|), 1, TC(s2, p2, |s|) + 1, m);
    }
  }
}

ghost function Wb(n: nat): nat
{
  8 * (n * (n + 2) + n + 1) + 4
}

ghost function Kb(n: nat): nat
{
  3 * Wb(n) + 30
}

method Walk(arrow: array<int>, start: int)
    returns (p: int, ghost steps: nat)
  requires forall i :: 0 <= i < arrow.Length ==> arrow[i] == 1 || arrow[i] == -1
  modifies arrow
  ensures forall i :: 0 <= i < arrow.Length ==> arrow[i] == 1 || arrow[i] == -1
  ensures steps <= Wb(arrow.Length)
{
  steps := 0;
  steps := steps + 1;
  var n := arrow.Length;
  p := start;
  ghost var p_zero := PF(arrow[..], p);
  PBound(arrow[..], p);
  while 0 <= p < n
    invariant n == arrow.Length
    invariant forall i :: 0 <= i < arrow.Length ==> arrow[i] == 1 || arrow[i] == -1
    invariant steps + 8 * PF(arrow[..], p) <= 1 + 8 * p_zero
    decreases PF(arrow[..], p)
  {
    ghost var before := arrow[..];
    ghost var p_old := p;
    steps := steps + 4;
    steps := steps + 1;
    var q := arrow[p];
    steps := steps + 2;
    arrow[p] := -q;
    steps := steps + 1;
    p := p + q;
    assert arrow[..] == before[p_old := -q];
    StepP(before, p_old);
  }
  steps := steps + 3;
}

method Solve(n: int, a_list: seq<int>)
    returns (output: string, ghost steps: nat)
  requires n >= 1 && |a_list| == n
  requires forall i :: 0 <= i < n ==> 0 <= a_list[i] <= 3
  ensures steps <= n * Kb(n) + 12 * n + 5 + 2 * |output|
{
  steps := 0;
  steps := steps + n;
  var arrow := new int[n];
  var k := 0;
  while k < n
    invariant 0 <= k <= n
    invariant arrow.Length == n
    invariant forall j :: 0 <= j < k ==> arrow[j] == 1
    invariant steps == n + 4 * k
    decreases n - k
  {
    steps := steps + 2;
    steps := steps + 1;
    arrow[k] := 1;
    steps := steps + 1;
    k := k + 1;
  }
  steps := steps + 1;
  var right := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant arrow.Length == n
    invariant forall j :: 0 <= j < n ==> arrow[j] == 1 || arrow[j] == -1
    invariant steps <= 5 * n + 1 + i * Kb(n)
    decreases n - i
  {
    steps := steps + 2;
    var t := 0;
    ghost var s_out := steps;
    while t < a_list[i]
      invariant 0 <= t <= a_list[i]
      invariant arrow.Length == n
      invariant forall j :: 0 <= j < n ==> arrow[j] == 1 || arrow[j] == -1
      invariant steps <= s_out + t * (Wb(n) + 6)
      decreases a_list[i] - t
    {
      steps := steps + 3;
      var p, s0 := Walk(arrow, i);
      steps := steps + s0;
      steps := steps + 1;
      if p == n {
        steps := steps + 1;
        right := right + 1;
      }
      steps := steps + 1;
      CostMulDistrib(t, 1, t + 1, Wb(n) + 6);
      t := t + 1;
    }
    CostMulMonoLeft(t, 3, Wb(n) + 6);
    steps := steps + 2;
    steps := steps + 1;
    CostMulDistrib(i, 1, i + 1, Kb(n));
    i := i + 1;
  }
  steps := steps + 1;
  var up := 0;
  k := 0;
  ghost var s_mid := steps;
  while k < n
    invariant 0 <= k <= n
    invariant arrow.Length == n
    invariant steps <= s_mid + 6 * k
    decreases n - k
  {
    steps := steps + 2;
    steps := steps + 2;
    if arrow[k] == 1 {
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
  assert i == n;
}

import opened Prelude
