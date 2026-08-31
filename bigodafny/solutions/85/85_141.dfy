// 1075_B. Taxi drivers and Lyft  (problem 85, solution 85_141)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, m = map(int, input().split())
// a = list(map(int, input().split()))
// s = list(map(int, input().split()))
// d = [0]*m
// f = []
// for q in range(len(s)):
//     if s[q] == 1:
//         f.append(a[q])
// q2, q1 = -float('inf'), f[0]
// q3, q4 = -1, 0
// for q in range(len(a)):
//     if s[q] == 1:
//         q2, q1 = a[q], f[q4+1] if len(f) > q4+1 else float('inf')
//         q3, q4 = q3+1, q4+1
//     else:
//         if q2 == -float('inf'):
//             d[q4] += 1
//         elif q1 == float('inf'):
//             d[q3] += 1
//         else:
//             if a[q]-q2 <= q1-a[q]:
//                 d[q3] += 1
//             else:
//                 d[q4] += 1
// print(*d)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c_list: seq<int>, d_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
