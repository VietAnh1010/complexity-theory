// p02721 AtCoder Beginner Contest 161 - Yutori  (problem 1369, solution 1369_14)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// N, K, C = map(int, input().split())
// S = input()
// left = []
// right = []
// i, j = 0, N-1
// while len(left) <= K-1:
//     if S[i] == "o":
//         left.append(i)
//         i += C+1
//     else:
//         i += 1
// while len(right) <= K-1:
//     if S[j] == "o":
//         right.append(j)
//         j -= C+1
//     else:
//         j -= 1
// right.sort()
// for n in range(K):
//     if left[n] == right[n]:
//         print(left[n] + 1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a: int, b: int, s: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
