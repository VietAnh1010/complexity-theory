// 1208_B. Uniqueness  (problem 2650, solution 2650_97)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def b_uniqueness(arr):
//     i = 0
//     j = len(arr) - 1
// 
//     last_pos = {}
//     for ind, elem in enumerate(arr):
//         last_pos[elem] = ind
// 
//     repeated_set = set()
//     while arr[j] not in repeated_set:
//         repeated_set.add(arr[j])
//         j -= 1
// 
//     repeated_set.clear()
//     ans = j + 1
//     while arr[i] not in repeated_set:
//         repeated_set.add(arr[i])
//         j = max(j, last_pos[arr[i]])
//         ans = min(ans, j - i)
//         i += 1
//         if i == len(arr):
//             break
//     return ans
//  
// num_elem = int(input())
// elem = input().split(" ")
// 
// print(b_uniqueness(elem))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
