// 1004_C. Sonya and Robots  (problem 1039, solution 1039_146)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// nums = list(map(int, input().split()))
// left = {}
// from collections import Counter
// left=Counter(nums)
// count = 0
// done = set()
// for i in nums:
//     left[i] -= 1
//     if left[i] == 0:
//         del left[i]
//     if i not in done:
//         count += len(left.keys())
//         done.add(i)
// 
// print(count)
// 	
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n_str: string, a_list_str: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
