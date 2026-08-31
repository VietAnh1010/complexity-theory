// 978_C. Letters  (problem 1180, solution 1180_626)
// time complexity: O(n+m)log(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n_dorm,n_letter = map(int,input().split())
// dorms = list(map(int,input().split()))[:n_dorm]
// lroom = list(map(int,input().split()))[:n_letter]
// d_left = 0
// d_right = len(dorms) - 1
// l_left = 0
// l_right = len(lroom) - 1
// lst = []
// new = 0
// while l_left <= l_right:
//     if lroom[l_left] <= dorms[d_left]:
//         lst.append([d_left+1] + [abs(new-lroom[l_left])])
//         l_left += 1
//     else:
//         d_left += 1
//         new = dorms[d_left-1]
//         dorms[d_left] += dorms[d_left - 1]
// for i in sorted(lst):
//     print(f"{i[0]} {i[1]}")  
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c_list: seq<int>, d_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
