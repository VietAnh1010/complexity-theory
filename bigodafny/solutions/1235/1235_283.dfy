// 1395_A. Boboniu Likes to Color Balls  (problem 1235, solution 1235_283)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def get_res(a, b, c, d):
//     if a==0 or b==0 or c==0:
//         l = [x%2 for x in [a,b,c,d]]
//         odds = sum(l)
//         if odds > 1:
//             return 'No'
//         else:
//             return 'Yes'
//     else:
//         l = [x%2 for x in [a,b,c,d]]
//         odds = sum(l)
//         if odds == 2:
//             return 'No'
//         else:
//             return 'Yes'
// 
// 
// n = int(input())
// for _ in range(n):
//     lis = list(map(lambda x: int(x), input().split()))
//     print(get_res(*lis))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, matrix: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
