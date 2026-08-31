// 1008_B. Turn the Rectangles  (problem 396, solution 396_361)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// dimensions = []
// flag = 1
// 
// while n > 0:
//     dimensions.append(list(map(int, input().split())))
//     n -= 1
// 
// maximum = max(dimensions[0])
// 
// for i in range(1, len(dimensions)):
//     if maximum >= max(dimensions[i]):
//         maximum = max(dimensions[i])
//         continue
//     elif maximum >= min(dimensions[i]):
//         maximum = min(dimensions[i])
//         continue
//     else:
//         flag = 0
//         break
// 
// if flag:
//     print("YES")
// else:
//     print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, rectangles: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
