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

ghost function Meas(ph: int, p: int, n: int): int
{
  if ph == 0 then 3 * (n - p) + 3
  else if ph == 1 then 3 * (n - p) - 1
  else if ph == 2 then 3 * (n - p) + 1
  else if ph == 3 then 3 * n + 3 * p + 12
  else if ph == 4 then 3 * n + 3 * p + 8
  else if ph == 5 then 3 * n + 3 * p + 10
  else if ph == 6 then 3 * n + 3 * p + 13
  else if ph == 7 then 6 * n + 16
  else 0
}

method Walk(mirror: array<int>, start: int)
    returns (p: int, ghost steps: nat)
  requires forall i :: 0 <= i < mirror.Length ==> mirror[i] == 0 || mirror[i] == 1
  modifies mirror
  ensures forall i :: 0 <= i < mirror.Length ==> mirror[i] == 0 || mirror[i] == 1
  ensures steps <= 66 * mirror.Length + 200
{
  steps := 0;
  steps := steps + 1;
  var n := mirror.Length;
  var d := 1;
  p := start;
  ghost var ph := 7;
  ghost var m0 := Meas(7, 0, n);
  while 0 <= p < n
    invariant 0 <= ph <= 8
    invariant forall x :: 0 <= x < n ==> mirror[x] == 0 || mirror[x] == 1
    invariant ph == 0 ==> d == 1 && 1 <= p <= n && mirror[p - 1] == 1
    invariant ph == 1 ==> d == -1 && 0 <= p <= n - 2 && mirror[p] == 1 && mirror[p + 1] == 0
    invariant ph == 2 ==> d == 1 && 0 <= p < n && mirror[p] == 0
    invariant ph == 3 ==> d == -1 && -1 <= p <= n - 2 && mirror[p + 1] == 1
    invariant ph == 4 ==> d == 1 && 1 <= p < n && mirror[p] == 1 && mirror[p - 1] == 0
    invariant ph == 5 ==> d == -1 && 0 <= p < n && mirror[p] == 0
    invariant ph == 6 ==> d == -1 && -1 <= p <= n - 1 && (p + 1 < n ==> mirror[p + 1] == 0)
    invariant ph == 7 ==> d == 1 && p == start
    invariant ph == 8 ==> p >= n
    invariant Meas(ph, p, n) >= 0
    invariant steps + 11 * Meas(ph, p, n) <= 1 + 11 * m0
    decreases Meas(ph, p, n)
  {
    ghost var oph := ph;
    ghost var om := mirror[p];
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
    if oph == 0 { ph := if om == 0 then 0 else 1; }
    else if oph == 1 { ph := 2; }
    else if oph == 2 { ph := 0; }
    else if oph == 3 { ph := if om == 0 then 3 else 4; }
    else if oph == 4 { ph := 5; }
    else if oph == 5 { ph := 3; }
    else if oph == 6 { ph := if om == 0 then 3 else (if p < n then 2 else 8); }
    else if oph == 7 { ph := if om == 0 then 0 else 6; }
  }
  steps := steps + 3;
}

method Solve(n: int, a_list: seq<int>)
    returns (output: string, ghost steps: nat)
  requires n >= 1 && |a_list| == n
  requires forall i :: 0 <= i < n ==> 0 <= a_list[i] <= 3
  ensures steps <= 14 * n + 3 + n * (198 * n + 623) + 2 * |output|
{
  steps := 0;
  ghost var Kc := 66 * n + 206;
  ghost var L := 3 * Kc + 5;
  steps := steps + n;
  var mirror := new int[n];
  var k := 0;
  while k < n
    invariant 0 <= k <= n
    invariant steps <= n + 5 * k
    invariant forall x :: 0 <= x < k ==> mirror[x] == 0
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
  ghost var sB := steps;
  while i < n
    invariant 0 <= i <= n
    invariant sB <= 6 * n + 1
    invariant steps <= sB + i * L
    invariant L == 198 * n + 623 && Kc == 66 * n + 206
    invariant mirror.Length == n
    invariant forall x :: 0 <= x < n ==> mirror[x] == 0 || mirror[x] == 1
    decreases n - i
  {
    steps := steps + 2;
    ghost var sI := steps;
    var t := 0;
    while t < a_list[i]
      invariant 0 <= t <= 3
      invariant a_list[i] <= 3
      invariant steps <= sI + t * Kc
      invariant Kc == 66 * n + 206
      invariant mirror.Length == n
      invariant forall x :: 0 <= x < n ==> mirror[x] == 0 || mirror[x] == 1
      decreases a_list[i] - t
    {
      steps := steps + 3;
      var p, s0 := Walk(mirror, i);
      steps := steps + s0;
      steps := steps + 1;
      if p == n {
        steps := steps + 1;
        right := right + 1;
      }
      steps := steps + 1;
      CostMulDistrib(t, 1, t + 1, Kc);
      t := t + 1;
    }
    CostMulMonoLeft(t, 3, Kc);
    steps := steps + 2;
    steps := steps + 1;
    CostMulDistrib(i, 1, i + 1, L);
    i := i + 1;
  }
  steps := steps + 1;
  ghost var sA := steps;
  var up := 0;
  k := 0;
  while k < n
    invariant 0 <= k <= n
    invariant steps <= sA + 7 * k
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
  steps := steps + (Digits(right) + |" "| + Digits(up) + |IntToString(up)|);
  output := IntToString(right) + " " + IntToString(up);
  IntToStringDigits(right);
  IntToStringDigits(up);
}

import opened Prelude
