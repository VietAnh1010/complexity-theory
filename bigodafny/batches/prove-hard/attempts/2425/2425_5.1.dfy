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

include "../../../../prelude.dfy"

method Solve(n: int, k: int, pairs: seq<(int, int)>)
    returns (output: string, ghost steps: nat)
    ensures steps <= 2 * NLogN(|pairs| + 1) + 11 * (|pairs| + 1) + 6 + |output|
{
  steps := 0;
  steps := steps + (2 + |[(0, -1)]|);
  var arr := pairs + [(0, -1)];
  steps := steps + SortCost(|arr|);
  var sortedDesc := Sort(arr, (x: (int, int), y: (int, int)) => x.0 > y.0 || (x.0 == y.0 && x.1 > y.1));
  var curr := k;
  var t := 0;
  var idx := 0;
  SortCostWithin(|arr|, |pairs| + 1);
  ghost var base := steps;
  while idx < |sortedDesc|
    invariant idx <= |sortedDesc| && |sortedDesc| == |pairs| + 1
    invariant base <= 3 + 2 * NLogN(|pairs| + 1) + 1
    invariant steps == base + 11 * idx
    decreases |sortedDesc| - idx
  {
    steps := steps + 3;
    steps := steps + 2;
    var xi := sortedDesc[idx].0;
    steps := steps + 2;
    var yi := sortedDesc[idx].1;
    steps := steps + 1;
    var d := curr - xi;
    curr := xi;
    steps := steps + 1;
    var cand := t + d;
    steps := steps + 2;
    t := if yi > cand then yi else cand;
    steps := steps + 1;
    idx := idx + 1;
  }
  steps := steps + 2;
  steps := steps + Digits(t);
  output := IntToString(t);
  IntToStringDigits(t);
}

import opened Prelude
