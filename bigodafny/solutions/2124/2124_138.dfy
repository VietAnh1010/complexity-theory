// 1077_A. Frog Jumping  (problem 2124, solution 2124_138)
// time complexity: O(n*m)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t = int(input())
// all_data = []
// 
// for i in range(t):
//     data = [int(i) for i in input().split(" ")]
//     all_data.append(data)
// 
// for i in all_data:
//     right = i[0]
//     left = i[1]
//     k = i[2]
//     jump = right-left
//     if k % 2 == 0:
//         print(jump*(k//2))
//     else:
//         print(jump*(k//2)+right)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, queries: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
