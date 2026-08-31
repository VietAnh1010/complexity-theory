// 357_A. Group of Students  (problem 894, solution 894_85)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// dumb = input()
// l = [int(o) for o in input().split()]
// x, y = [int(o) for o in input().split()]
// 
// def Valid(l, k, x, y):
//     s = 0
//     for i in range(k):
//         s += l[i]
//         if s >= x and s <= y and sum(l) - s >= x and sum(l) - s <= y and s != sum(l) and s != 0 and sum(l) - s != 0:
//             return True
//     return False
// 
// for i in range(len(l)):
//     if Valid(l, i, x, y):
//         break
// if i+1 > 0 and i < len(l) and Valid(l, i, x, y):
//     print(i+1)
// else:
//     print(0)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>, x: int, y: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
