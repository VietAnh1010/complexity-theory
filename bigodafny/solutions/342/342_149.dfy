// 1113_B. Sasha and Magnetic Machines  (problem 342, solution 342_149)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// 
// 
// n = int(input())
// arr_str = input().split()
// 
// arr = [int(x) for x in arr_str]
// 
// 
// min_el = arr[0]
// s = 0
// 
// for x in arr:
//     s += x
//     if x < min_el:
//         min_el = x
// 
// diff = 0
// 
// 
// for x in arr:
//     if x == min_el:
//         continue
//     for y in range(2, x // 2 + 1):
//         if x % y == 0:
//             new_x = x // y
//             new_min = min_el*y
//             new_diff = x + min_el - new_x - new_min
//             if new_diff > diff:
//                 diff = new_diff
// 
// print(s - diff)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
