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
  var signs: seq<int> := [];
  var nums: seq<int> := [];
  var dens: seq<int> := [];
  var i := 0;
  while i < |d_list|
    decreases |d_list| - i
  {
    var dx := d_list[i].0 - b;
    var dy := d_list[i].1 - c;
    var num := dx * dx;
    var den := dx * dx + dy * dy;
    var sgn := if dx * dy >= 0 then 1 else -1;
    signs := signs + [sgn];
    nums := nums + [num];
    dens := dens + [den];
    i := i + 1;
  }
  var count := 0;
  i := 0;
  while i < |d_list|
    decreases |d_list| - i
  {
    var isNew := true;
    var j := 0;
    while j < i
      decreases i - j
    {
      if signs[j] == signs[i] && nums[i] * dens[j] == nums[j] * dens[i] {
        isNew := false;
      }
      j := j + 1;
    }
    if isNew { count := count + 1; }
    i := i + 1;
  }
  output := IntToString(count);
}
