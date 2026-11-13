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

method Walk(mark: array<int>, start: int)
    returns (p: int, ghost steps: nat)
  requires forall i :: 0 <= i < mark.Length ==> mark[i] == 0 || mark[i] == 1
  modifies mark
  ensures forall i :: 0 <= i < mark.Length ==> mark[i] == 0 || mark[i] == 1
  decreases *
{
  steps := 0;
  steps := steps + 1;
  var n := mark.Length;
  var d := 1;
  p := start;
  while 0 <= p < n
    invariant forall i :: 0 <= i < mark.Length ==> mark[i] == 0 || mark[i] == 1
    invariant d == 1 || d == -1
    decreases *
  {
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
  }
  steps := steps + 3;
}

method Solve(n: int, a_list: seq<int>)
    returns (output: string, ghost steps: nat)
  requires n >= 1 && |a_list| == n
  requires forall i :: 0 <= i < n ==> 0 <= a_list[i] <= 3
  decreases *
{
  steps := 0;
  steps := steps + n;
  var mark := new int[n];
  var k := 0;
  while k < n
    invariant 0 <= k <= n
    invariant forall j :: 0 <= j < k ==> mark[j] == 1
    invariant forall j :: k <= j < n ==> mark[j] == 0 || mark[j] == 1
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
  while i < n
    invariant forall j :: 0 <= j < mark.Length ==> mark[j] == 0 || mark[j] == 1
    decreases *
  {
    steps := steps + 2;
    var t := 0;
    while t < a_list[i]
      invariant forall j :: 0 <= j < mark.Length ==> mark[j] == 0 || mark[j] == 1
      decreases *
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
      t := t + 1;
    }
    steps := steps + 2;
    steps := steps + 1;
    i := i + 1;
  }
  steps := steps + 1;
  var up := 0;
  k := 0;
  while k < n
    decreases *
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
}

import opened Prelude
