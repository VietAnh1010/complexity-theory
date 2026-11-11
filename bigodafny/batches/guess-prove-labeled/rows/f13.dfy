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

include "../../../prelude.dfy"
import opened Prelude

method Walk(mirror: array<int>, start: int) returns (p: int)
  modifies mirror
  requires forall i :: 0 <= i < mirror.Length ==> mirror[i] == 0 || mirror[i] == 1
  decreases *
{
  var n := mirror.Length;
  var d := 1;
  p := start;
  while 0 <= p < n
    decreases *
  {
    if mirror[p] == 1 {
      d := -d;
    }
    mirror[p] := 1 - mirror[p];
    p := p + d;
  }
}

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires n >= 1 && |a_list| == n
  requires forall i :: 0 <= i < n ==> 0 <= a_list[i] <= 3
  decreases *
{
  var mirror := new int[n];
  var k := 0;
  while k < n
    decreases *
  {
    mirror[k] := 0;
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
      var p := Walk(mirror, i);
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
    if mirror[k] == 1 {
      up := up + 1;
    }
    k := k + 1;
  }
  output := IntToString(right) + " " + IntToString(up);
}
