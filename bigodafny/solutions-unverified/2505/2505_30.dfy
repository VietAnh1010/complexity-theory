// 886_C. Petya and Catacombs  (problem 2505, solution 2505_30)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// data = list(map(int, input().split()))
// d = [False] * (n + 4)
// d[0] = True
// res = 1
// for i in range(n):
//     #print(d)
//     if d[data[i]]:
//         d[data[i]] = False
//         d[i + 1] = True
//     else:
//         d[i + 1] = True
//         res += 1
// #print(d)
// print(res)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, coordinates: seq<seq<int>>) returns (output: string)
  requires n >= 0
  requires |coordinates| >= 1
  requires n <= |coordinates[0]|
  requires forall t :: 0 <= t < n ==> 0 <= coordinates[0][t] < n + 4
{
  var data := coordinates[0];
  var d: seq<bool> := [];
  var z := 0;
  while z < n + 4
    invariant 0 <= z <= n + 4
    invariant |d| == z
    decreases n + 4 - z
  {
    d := d + [false];
    z := z + 1;
  }
  d := d[0 := true];
  var res := 1;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |d| == n + 4
    decreases n - i
  {
    if d[data[i]] {
      d := d[data[i] := false];
      d := d[i + 1 := true];
    } else {
      d := d[i + 1 := true];
      res := res + 1;
    }
    i := i + 1;
  }
  output := IntToString(res);
}
