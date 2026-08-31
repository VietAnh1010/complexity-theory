// 486_C. Palindrome Transformation  (problem 1387, solution 1387_19)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, p = map(int, input().split())
// p -= 1
// s = input()
// ans = 0
// idx = 0
// pos = []
// while idx < n//2:
//     if s[idx] != s[n-1-idx]:
//         diff = abs(ord(s[idx]) - ord(s[n-1-idx]))
//         ans += min(diff, 26 - diff)
//         if p >= n//2:
//             pos.append(n-1-idx)
//         else:
//             pos.append(idx)
//     idx += 1
// pos.sort()
// #print(ans)
// 
// if ans == 0:
//     print(0)
// elif len(pos) == 1:
//     ans += abs(p - pos[0])
//     print(ans)
// else:
//     if abs(p - pos[0]) < abs(p - pos[-1]):
//         ans += abs(p - pos[0]) + (pos[-1] - pos[0])
//     else:
//         ans += abs(p - pos[-1]) + (pos[-1] - pos[0])
// 
//     print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, s: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
