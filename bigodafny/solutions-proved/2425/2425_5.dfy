// 608_A. Saitama Destroys Hotel  (problem 2425, solution 2425_5)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// k = []
// a, b = map(int, input().split(' '))
// for i in range(a):
//     x, y = map(int, input().split(' '))
//     k.append([x,y])
// k.append([0, -1])
// k.sort()
// k.reverse()
//
// curr = b
// t = 0
// for i in k:
//     d = curr - i[0]
//     curr = i[0]
//     t = max(i[1], t+d)
// print(t)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// ---- proof-only scaffolding for the complexity bound (see
// solutions-proved/nlogn/603/603_284.dfy for the same argument) ----------

method Solve(n: int, k: int, pairs: seq<(int, int)>) returns (output: string, ghost steps: nat)
  requires n >= 0 && n == |pairs|
  ensures steps <= 2 * (n + 1) * (CeilLog2(n + 1) + 1) + 5 * (n + 1) + 5
{
  steps := 1;
  var arr := pairs + [(0, -1)];
  steps := steps + 1;
  var m := |arr|;
  SortCostTreeBound(m);
  steps := steps + SortCost(m);
  var sortedDesc := Sort(arr, (x: (int, int), y: (int, int)) => x.0 > y.0 || (x.0 == y.0 && x.1 > y.1));
  assert |sortedDesc| == m;

  var curr := k;
  var t := 0;
  var idx := 0;
  while idx < |sortedDesc|
    invariant 0 <= idx <= |sortedDesc|
    invariant steps <= 1 + 1 + SortCost(m) + 4 * idx
    decreases |sortedDesc| - idx
  {
    var xi := sortedDesc[idx].0;
    var yi := sortedDesc[idx].1;
    var d := curr - xi;
    curr := xi;
    var cand := t + d;
    t := if yi > cand then yi else cand;
    idx := idx + 1;
    steps := steps + 4;
  }
  output := IntToString(t);
  steps := steps + 1;
}
