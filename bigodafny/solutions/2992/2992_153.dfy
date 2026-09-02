// 450_A. Jzzhu and Children  (problem 2992, solution 2992_153)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// n = input().split()
// a = int(n[0])
// b = int(n[1])
// c = []
// t = input().split()
// for i in range(a):
//     c.append([int(t[i]),0,int(i)])
//     c[i][1] = math.ceil(c[i][0] / b)
// c.sort(key = lambda x:(x[1],x[2]))
// print(c[-1][2]+1)
//        
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, a_list: seq<int>) returns (output: string)
{
  var c: seq<(int, int, int)> := [];
  var i := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    decreases |a_list| - i
  {
    var v := a_list[i];
    var ceilVal := if k != 0 then (v + k - 1) / k else 0;
    c := c + [(v, ceilVal, i)];
    i := i + 1;
  }
  var sorted := Sort(c, (x: (int, int, int), y: (int, int, int)) =>
    x.1 < y.1 || (x.1 == y.1 && x.2 < y.2));
  if |sorted| > 0 {
    output := IntToString(sorted[|sorted| - 1].2 + 1);
  } else {
    output := IntToString(0);
  }
}
