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

lemma RoomStep(r: nat, c: nat)
  requires r >= 1
  ensures (r - 1) * c + c == r * c
{
  CostMulDistrib(r - 1, 1, r, c);
}

lemma SqLem(n: nat)
  requires n >= 1
  ensures (n - 1) * (n + 1) + 1 == n * n
{
  CostMulDistrib(n - 1, 1, n, n + 1);
  CostMulDistrib(n, 1, n + 1, n);
}

method Walk(arrow: array<int>, start: int)
    returns (p: int, ghost steps: nat)
  requires forall i :: 0 <= i < arrow.Length ==> arrow[i] == 1 || arrow[i] == -1
  ensures forall i :: 0 <= i < arrow.Length ==> arrow[i] == 1 || arrow[i] == -1
  ensures steps <= 8 * (arrow.Length * arrow.Length) + 4
  modifies arrow
{
  steps := 0;
  steps := steps + 1;
  var n := arrow.Length;
  p := start;
  ghost var inr: bool := 0 <= start < n;
  ghost var lo: int := if inr then start else 0;
  ghost var hi: int := lo;
  ghost var rgt: bool := inr && arrow[start] == 1;
  ghost var sp: int := if inr then (if arrow[start] == 1 then start else start + 1) else 0;
  ghost var it: nat := 0;
  ghost var room: nat := if inr then n - 1 else 0;
  ghost var dist: nat := 1;
  ghost var rc: int := room * (n + 1);
  if inr { SqLem(n); }
  while 0 <= p < n
    invariant steps == 1 + 8 * it
    invariant forall i :: 0 <= i < n ==> arrow[i] == 1 || arrow[i] == -1
    invariant !inr ==> it == 0
    invariant it == 0 ==> p == start
    invariant inr ==> 0 <= lo <= hi < n && lo <= sp <= hi + 1
    invariant inr ==> forall k :: 0 <= k < n && lo <= k < sp ==> arrow[k] == -1
    invariant inr ==> forall k :: 0 <= k < n && sp <= k <= hi ==> arrow[k] == 1
    invariant inr ==> p == (if rgt then sp else sp - 1)
    invariant inr ==> room == n - (hi - lo + 1)
    invariant inr ==> dist == (if rgt then hi + 1 - p else p + 1 - lo)
    invariant rc == room * (n + 1)
    invariant inr ==> it + rc + dist <= n * n
    decreases room, dist
  {
    ghost var p0 := p;
    steps := steps + 4;
    steps := steps + 1;
    var q := arrow[p];
    assert inr;
    assert rgt ==> p0 == sp;
    assert (rgt && p0 <= hi) ==> q == 1;
    assert !rgt ==> p0 == sp - 1;
    assert (!rgt && lo <= p0) ==> q == -1;
    steps := steps + 2;
    arrow[p] := -q;
    steps := steps + 1;
    p := p + q;
    if rgt && q == 1 && p0 <= hi {
      sp := p0 + 1;
      dist := dist - 1;
    } else if rgt && q == 1 {
      RoomStep(room, n + 1);
      hi := p0; sp := p0 + 1; room := room - 1; rc := rc - (n + 1); dist := 0;
    } else if rgt {
      RoomStep(room, n + 1);
      hi := p0; sp := p0; rgt := false; dist := p0 - lo; room := room - 1; rc := rc - (n + 1);
    } else if q == -1 && lo <= p0 {
      sp := p0;
      dist := dist - 1;
    } else if q == -1 {
      RoomStep(room, n + 1);
      lo := p0; sp := p0; dist := 0; room := room - 1; rc := rc - (n + 1);
    } else {
      RoomStep(room, n + 1);
      lo := p0; sp := p0 + 1; rgt := true; dist := hi - p0; room := room - 1; rc := rc - (n + 1);
    }
    it := it + 1;
  }
  CostMulMonoLeft(0, room, n + 1);
  steps := steps + 3;
}

method Solve(n: int, a_list: seq<int>)
    returns (output: string, ghost steps: nat)
  requires n >= 1 && |a_list| == n
  requires forall i :: 0 <= i < n ==> 0 <= a_list[i] <= 3
  ensures steps <= n * (24 * (n * n) + 35) + 11 * n + 3 + 2 * |output|
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
  CostMulMonoLeft(0, n, n);
  ghost var nn: nat := n * n;
  ghost var w: nat := 8 * nn + 10;
  ghost var kout: nat := 3 * w + 5;
  ghost var s2 := steps;
  var right := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant arrow.Length == n
    invariant forall j :: 0 <= j < n ==> arrow[j] == 1 || arrow[j] == -1
    invariant steps <= s2 + i * kout
    decreases n - i
  {
    steps := steps + 2;
    var t := 0;
    ghost var sb := steps;
    while t < a_list[i]
      invariant 0 <= t <= a_list[i]
      invariant arrow.Length == n
      invariant forall j :: 0 <= j < n ==> arrow[j] == 1 || arrow[j] == -1
      invariant steps <= sb + t * w
      decreases a_list[i] - t
    {
      steps := steps + 3;
      var p, s0 := Walk(arrow, i);
      assert arrow.Length * arrow.Length == nn;
      steps := steps + s0;
      steps := steps + 1;
      if p == n {
        steps := steps + 1;
        right := right + 1;
      }
      steps := steps + 1;
      CostMulDistrib(t, 1, t + 1, w);
      t := t + 1;
    }
    CostMulMonoLeft(a_list[i], 3, w);
    steps := steps + 2;
    steps := steps + 1;
    CostMulDistrib(i, 1, i + 1, kout);
    i := i + 1;
  }
  steps := steps + 1;
  ghost var s3 := steps;
  var up := 0;
  k := 0;
  while k < n
    invariant 0 <= k <= n
    invariant arrow.Length == n
    invariant steps <= s3 + 6 * k
    invariant forall j :: 0 <= j < n ==> arrow[j] == 1 || arrow[j] == -1
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
  IntToStringDigits(right);
  IntToStringDigits(up);
  steps := steps + (Digits(right) + |" "| + Digits(up) + |IntToString(up)|);
  output := IntToString(right) + " " + IntToString(up);
  assert |output| == |IntToString(right)| + 1 + |IntToString(up)|;
  assert kout == 24 * nn + 35;
}

import opened Prelude
