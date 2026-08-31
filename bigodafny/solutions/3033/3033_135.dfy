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
  output := ""; // TODO: translate the Python above
}
