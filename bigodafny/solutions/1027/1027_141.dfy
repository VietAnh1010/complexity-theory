// 514_B. Han Solo and Lazer Gun  (problem 1027, solution 1027_141)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import itertools
// 
// n, x0, y0 = [int(x) for x in input().split()]
// target = []
// for i in range(n):
//     x, y = [int(x) for x in input().split()]
//     cos2 = (x-x0)**2 / ((x-x0)**2 + (y-y0)**2)
//     target.append(cos2 if (x-x0)*(y-y0) >= 0 else -cos2)
// 
// target.sort()
// L = list(itertools.groupby(target))
// print(len(L))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c: int, d_list: seq<(int, int)>) returns (output: string)
{
  // target[i] = (numerator, denominator) of the signed cos2, denominator > 0
  var target: seq<(int, int)> := [];
  var i := 0;
  while i < |d_list|
    invariant 0 <= i <= |d_list|
    decreases |d_list| - i
  {
    var dx := d_list[i].0 - b;
    var dy := d_list[i].1 - c;
    var num := dx * dx;
    var den := dx * dx + dy * dy;
    var v := if dx * dy >= 0 then num else -num;
    target := target + [(v, den)];
    i := i + 1;
  }
  var sorted := Sort(target, (p: (int, int), q: (int, int)) => p.0 * q.1 < q.0 * p.1);
  // itertools.groupby: one group per run of equal values
  var count := 0;
  i := 0;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    decreases |sorted| - i
  {
    if i == 0 || sorted[i].0 * sorted[i - 1].1 != sorted[i - 1].0 * sorted[i].1 {
      count := count + 1;
    }
    i := i + 1;
  }
  output := IntToString(count);
}
