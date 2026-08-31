// 1328_B. K-th Beautiful String  (problem 2819, solution 2819_55)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// input = sys.stdin.readline
// 
// for _ in range(int(input())):
//     n, k = map(int, input().split())
//     ans = ['a']*n
//     for i, right in zip(range(n-2, -1, -1), range(1, n+1)):
//         if k > right:
//             k -= right
//             continue
//         j = n
//         while k:
//             k -= 1
//             j -= 1
// 
//         ans[i] = ans[j] = 'b'
//         break
// 
//     print(*ans, sep='')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs_list: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
