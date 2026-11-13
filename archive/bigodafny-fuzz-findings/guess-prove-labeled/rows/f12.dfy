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

include "../../../prelude.dfy"
import opened Prelude

method Walk(arrow: array<int>, start: int) returns (p: int)
  modifies arrow
  requires forall i :: 0 <= i < arrow.Length ==> arrow[i] == 1 || arrow[i] == -1
  decreases *
{
  var n := arrow.Length;
  p := start;
  while 0 <= p < n
    decreases *
  {
    var q := arrow[p];
    arrow[p] := -q;
    p := p + q;
  }
}

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires n >= 1 && |a_list| == n
  requires forall i :: 0 <= i < n ==> 0 <= a_list[i] <= 3
  decreases *
{
  var arrow := new int[n];
  var k := 0;
  while k < n
    decreases *
  {
    arrow[k] := 1;
    k := k + 1;
  }
  var right := 0;
  var i := 0;
  while i < n
    decreases *
  {
    var t := 0;
    while t < a_list[i]
      decreases *
    {
      var p := Walk(arrow, i);
      if p == n {
        right := right + 1;
      }
      t := t + 1;
    }
    i := i + 1;
  }
  var up := 0;
  k := 0;
  while k < n
    decreases *
  {
    if arrow[k] == 1 {
      up := up + 1;
    }
    k := k + 1;
  }
  output := IntToString(right) + " " + IntToString(up);
}
