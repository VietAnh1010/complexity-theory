// 1130_B. Two Cakes  (problem 3033, solution 3033_135)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// class House:
//     c = 0
// 
//     def __init__(self, val):
//         self.id = House.c + 1
//         self.val = int(val)
//         House.c += 1
// 
// n = int(input())
// a = list(map(House, input().split()))
// a.sort(key=lambda x: x.val)
// length = 0
// pos1 = pos2 = 1
// for i in range(n * 2):
//     if i % 2:
//         length += abs(pos2 - a[i].id)
//         pos2 = a[i].id
//     else:
//         length += abs(pos1 - a[i].id)
//         pos1 = a[i].id
// print(length)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, edges_list: seq<int>) returns (output: string)
{
  var a := edges_list;
  var pairs: seq<(int, int)> := seq(|a|, i requires 0 <= i < |a| => (a[i], i + 1));
  var sorted := Sort(pairs, (x: (int, int), y: (int, int)) => x.0 < y.0);
  var length := 0;
  var pos1 := 1;
  var pos2 := 1;
  var i := 0;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    decreases |sorted| - i
  {
    var id := sorted[i].1;
    if i % 2 == 1 {
      length := length + AbsInt(pos2 - id);
      pos2 := id;
    } else {
      length := length + AbsInt(pos1 - id);
      pos1 := id;
    }
    i := i + 1;
  }
  output := IntToString(length);
}
