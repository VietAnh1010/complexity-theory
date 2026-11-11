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

include "../../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires n >= 1 && |a_list| == n
  requires forall i :: 0 <= i < n ==> 0 <= a_list[i] <= 3
  decreases *
{
  var alive := new int[n];
  var k := 0;
  while k < n
    decreases *
  {
    alive[k] := 1;
    k := k + 1;
  }
  var p := n - 1;
  var t := 0;
  while t < n
    decreases *
  {
    var s := a_list[t] + 1;
    while s > 0
      decreases *
    {
      p := (p + 1) % n;
      if alive[p] == 1 {
        s := s - 1;
      }
    }
    alive[p] := 0;
    t := t + 1;
  }
  output := IntToString(p + 1);
}
