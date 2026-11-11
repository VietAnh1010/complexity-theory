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

include "../../../prelude.dfy"
import opened Prelude

method Walk(mark: array<int>, start: int) returns (p: int)
  modifies mark
  requires forall i :: 0 <= i < mark.Length ==> mark[i] == 0 || mark[i] == 1
  decreases *
{
  var n := mark.Length;
  var d := 1;
  p := start;
  while 0 <= p < n
    decreases *
  {
    var bounce := mark[p] == 1;
    if d == -1 {
      mark[p] := 1;
    } else {
      mark[p] := 0;
    }
    if bounce {
      d := -d;
    }
    p := p + d;
  }
}

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires n >= 1 && |a_list| == n
  requires forall i :: 0 <= i < n ==> 0 <= a_list[i] <= 3
  decreases *
{
  var mark := new int[n];
  var k := 0;
  while k < n
    decreases *
  {
    mark[k] := 1;
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
      var p := Walk(mark, i);
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
    if mark[k] == 1 {
      up := up + 1;
    }
    k := k + 1;
  }
  output := IntToString(right) + " " + IntToString(up);
}
