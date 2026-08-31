// 1075_B. Taxi drivers and Lyft  (problem 85, solution 85_71)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def binary_search(array, target):
//     lower = 0
//     upper = len(array) - 1
//     if upper == lower:
//         return 0
//     while lower < upper:   # use < instead of <=
//         x = lower + (upper - lower) // 2
//         val = array[x]
//         if target == val:
//             return x
//         elif target > val:
//             if lower == x:   # these two are the actual lines
//                 dist_left = target - array[lower]
//                 dist_right = array[upper] - target
//                 if dist_left == dist_right or dist_left < dist_right:
//                     return lower
//                 elif dist_left > dist_right:
//                     return upper
//             lower = x
//         elif target < val:
//             upper = x
//             if lower == upper:
//                 return lower
// 
// 
// R = input()
// 
// x = list(map(int, input().split()))
// t = list(map(int, input().split()))
// 
// passengers = []
// taxis = []
// 
// for idx, val in enumerate(t):
//     if val == 0:
//         passengers.append(x[idx])
//     elif val == 1:
//         taxis.append(x[idx])
// 
// passengers.sort()
// taxis.sort()
// answer = [0] * len(taxis)
// 
// for i in passengers:
//     index = binary_search(taxis, i)
//     answer[index] += 1
// 
// ##
// print (' '.join(str(x) for x in answer ))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c_list: seq<int>, d_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
